import { Container, ContainerProxy } from "@cloudflare/containers";

// The platform calls this to route the container's outgoing requests to the handler below.
export { ContainerProxy };

interface Env extends Record<string, unknown> {
  CHARTER: DurableObjectNamespace<CharterServer>;
  MIRROR: R2Bucket;
  ANTHROPIC_API_KEY?: string;
}

const PORT = 8080;
/** How long a new container may take to read every game back from R2. */
const READY_TIMEOUT_MS = 120_000;
/** Only the container sends requests to this name, and they stop at this Worker. */
const MIRROR_HOST = "charter-mirror.internal";

/** One Worker and one Durable Object in front of one container for all games. */
export class CharterServer extends Container<Env> {
  defaultPort = PORT;
  // Tables pause after 3 minutes with nobody there. This lets the container sleep 10 minutes after the
  // last request, and the logs in R2 bring every game back.
  sleepAfter = "10m";

  constructor(ctx: DurableObjectState<{}>, env: Env) {
    super(ctx, env);
    const passed: Record<string, string> = {};
    for (const [k, v] of Object.entries(env)) {
      if (k.startsWith("CHARTER_") && typeof v === "string") passed[k] = v;
    }
    this.envVars = {
      ...passed,
      CHARTER_MIRROR_URL: `http://${MIRROR_HOST}`,
      // Only this Worker can reach the container, and it sets the header below.
      CHARTER_TRUST_CLIENT_IP: "1",
      ...(env.ANTHROPIC_API_KEY ? { ANTHROPIC_API_KEY: env.ANTHROPIC_API_KEY } : {}),
    };
  }

  override async fetch(request: Request): Promise<Response> {
    // Until the container is healthy, wait the longer time. The class's own wait is too short for a
    // restore, and a request that arrives during one must wait for it too.
    if (!this.ctx.container?.running || (await this.getState()).status !== "healthy") {
      await this.startAndWaitForPorts({
        ports: PORT,
        cancellationOptions: { portReadyTimeoutMS: READY_TIMEOUT_MS, abort: request.signal },
      });
    }
    return this.containerFetch(request, PORT);
  }

  override onStop(params: { exitCode: number; reason: string }): void {
    console.log(`container stopped: exit ${params.exitCode}, ${params.reason}`);
  }

  override onError(error: unknown): void {
    console.error("container error:", error);
  }
}

CharterServer.outboundByHost = {
  [MIRROR_HOST]: (request: Request, env: Env) => mirror(request, env.MIRROR),
};

const KEY = /^v1\/[A-Za-z0-9_-]+\.(db|talk|clerk|seats|ledger)\/\d{12}-\d{12}\.jsonl$/;

/** The server's copy of its logs. The container holds no R2 key: this binding does the work. */
async function mirror(request: Request, bucket: R2Bucket): Promise<Response> {
  const url = new URL(request.url);
  if (url.pathname === "/list" && request.method === "GET") {
    const page = await bucket.list({ prefix: "v1/", cursor: url.searchParams.get("cursor") ?? undefined });
    return Response.json({
      keys: page.objects.map((o) => o.key),
      cursor: page.truncated ? encodeURIComponent(page.cursor) : null,
    });
  }
  const key = url.pathname.startsWith("/o/") ? url.pathname.slice(3) : "";
  if (!KEY.test(key)) return new Response("bad key", { status: 400 });
  switch (request.method) {
    case "GET": {
      const object = await bucket.get(key);
      return object ? new Response(object.body) : new Response("not found", { status: 404 });
    }
    case "PUT":
      await bucket.put(key, await request.arrayBuffer());
      return new Response("ok");
    case "DELETE":
      await bucket.delete(key);
      return new Response("ok");
    default:
      return new Response("method not allowed", { status: 405 });
  }
}

export default {
  async fetch(request: Request, env: Env): Promise<Response> {
    const url = new URL(request.url);
    const isLocal = url.hostname === "localhost" || url.hostname === "127.0.0.1";
    // Seat tokens travel in requests, so nothing is served over plain HTTP.
    if (url.protocol === "http:" && !isLocal) {
      url.protocol = "https:";
      return Response.redirect(url.toString(), 301);
    }
    const headers = new Headers(request.headers);
    // This replaces anything a client sent under this name, so the budget cannot be dodged by lying.
    headers.set("x-charter-client-ip", request.headers.get("cf-connecting-ip") ?? "unknown");
    return env.CHARTER.getByName("singleton").fetch(new Request(request, { headers }));
  },
};

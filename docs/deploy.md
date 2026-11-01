# Deploying Charter on Cloudflare

One Worker and one Durable Object in front of one container, which holds every table. The container's disk does not last, so each game's logs are copied to an R2 bucket. A new container reads them back before it serves anyone.

## What you need

- A Cloudflare account on the Workers Paid plan.
- Docker running on this computer, and Node.
- An Anthropic API key, from a Console workspace of its own with a spend limit. That limit is the real ceiling on what this server can cost you. The budgets below are estimates.

## First deploy

Run these from the `cloudflare/` folder.

```
npm ci
npx wrangler login
npx wrangler r2 bucket create charter-logs
npx wrangler secret put ANTHROPIC_API_KEY
npx wrangler deploy
```

The last command prints the address, `https://charter.<your-subdomain>.workers.dev`. Wait a few minutes after the first deploy before you expect the game to answer, because Cloudflare is still preparing the container.

To play: open the address, found a table, and send friends the table code. No page lists the tables.

## Trying a build first

Cloudflare has no version URLs for Workers with containers, so the preview is a second Worker, `charter-preview`, with its own container and bucket. Its games stay apart, and its budgets are lower. It adds nothing to the fixed monthly price, and it costs usage only while awake.

```
npx wrangler r2 bucket create charter-logs-preview
npx wrangler secret put ANTHROPIC_API_KEY --env preview
npx wrangler deploy --env preview
```

It prints `https://charter-preview.<your-subdomain>.workers.dev`. To remove it, run `npx wrangler delete --env preview`.

## Settings

These are under `vars` in `cloudflare/wrangler.jsonc`. Change a value and run `npx wrangler deploy`. A new container uses the new value.

| Name | Default | Meaning |
|---|---|---|
| `CHARTER_BUDGET_DAILY_USD` | 500 | The most Claude can spend in a day, for the whole server. |
| `CHARTER_BUDGET_PER_IP_USD` | 100 | The most one IP address can spend in a day. |
| `CHARTER_GAMES_PER_DAY` | 500 | New tables a day, for the whole server. This limits storage, not spending. |
| `CHARTER_GAMES_PER_IP_DAY` | 100 | New tables a day, for one IP address. |
| `CHARTER_TABLE_AWAY_MS` | 180000 | A table pauses after this long with none of its people there. |
| `CHARTER_DESCRIBE_MODEL` | `claude-sonnet-5-5` | The model that writes a law's description. |
| `CHARTER_DESCRIBE_EFFORT` | `low` | The effort of that call. |
| `CHARTER_PRICE_INPUT_USD` | 4 | Dollars per million input tokens, for Opus and for any model with no prices of its own. |
| `CHARTER_PRICE_OUTPUT_USD` | 20 | Dollars per million output tokens, the same way. |
| `CHARTER_PRICE_CACHE_READ_USD` | 0.20 | Dollars per million cache-read tokens, the same way. |
| `CHARTER_PRICE_CACHE_WRITE_USD` | 5 | Dollars per million cache-write tokens, the same way. |
| `CHARTER_PRICE_HAIKU_INPUT_USD` | 0.10 | Dollars per million input tokens, for a model whose name starts with `claude-haiku`. |
| `CHARTER_PRICE_HAIKU_OUTPUT_USD` | 0.50 | Dollars per million output tokens, the same way. |
| `CHARTER_PRICE_HAIKU_CACHE_READ_USD` | 0.005 | Dollars per million cache-read tokens, the same way. This is an estimate. The description call uses no cache. |
| `CHARTER_PRICE_HAIKU_CACHE_WRITE_USD` | 0.125 | Dollars per million cache-write tokens, the same way. This is an estimate. |
| `CHARTER_PRICE_SONNET_INPUT_USD` | 2 | Dollars per million input tokens, for a model whose name starts with `claude-sonnet`. |
| `CHARTER_PRICE_SONNET_OUTPUT_USD` | 10 | Dollars per million output tokens, the same way. |
| `CHARTER_PRICE_SONNET_CACHE_READ_USD` | 0.20 | Dollars per million cache-read tokens, the same way. |
| `CHARTER_PRICE_SONNET_CACHE_WRITE_USD` | 2.50 | Dollars per million cache-write tokens, the same way. |

Each request is priced by the model it went to. The first four prices are the list prices of `claude-opus-5-5`. They also apply to a model the server does not know, so that it cannot count too little. If you use a dearer model, such as a Fable model, set them to its prices.

**The budgets are estimates.** The server multiplies the tokens the API reports by these prices, so a real bill can differ. A request already running can pass a budget by a little. A day is a UTC day. The server's total survives a restart. The per-address figures do not, so a restart resets them.

When a budget is reached the game keeps playing. The clerk says it is resting, Claude seats pass their turns, and people can still write formal text themselves. No description call is made, so a new law shows its rule source with a short note.

There are no accounts, so an IP address stands for a person, and friends sharing a connection share a budget. The server keeps only a salted hash of each address, in memory, and never logs it. A table's Claude spending counts against the last address to ask for Claude at that table.

A backup API key is not built. It would go in `Formalize.settings` in `Server/Formalize.lean`, which chooses the key, and `failureOf` in the same file names the errors that would switch to it.

## What happens when people leave

- **A table with people** pauses when none of its people has had the page open for 3 minutes. Bots and Claude seats stop, and no turn timer runs. When someone returns, the table goes on and the current turn gets a whole new deadline. If even one person is there, the timer still ends the turn of an idle seat.
- **A hidden tab** counts as present. It checks in every 30 seconds for 10 minutes and then stops.
- **The container** sleeps 10 minutes after the last request. The next visitor wakes it, and every game comes back from R2.
- **After any restart,** no table with people moves until one of them returns. A table of Claude seats and no people waits for someone to watch it. A table of bots and no people goes on by itself. Waking up spends nothing.

## What can be lost

| Event | What is lost |
|---|---|
| The container sleeps, or a deploy replaces it | Nothing. On SIGTERM the server copies everything to R2 and then exits. |
| The container is killed with no warning | Rows accepted since the last copy: about 1 second, plus one upload. |
| R2 is out of reach | The game keeps playing and the log says so. Nothing is lost unless the container dies before R2 returns. |

What survives is always the start of each log, so a game comes back at a real earlier position. A client that saw a lost event simply sees the game at the earlier position.

## Looking at logs

Open the Cloudflare dashboard, then Workers & Pages, `charter`, Containers, and the instance's logs. Requests are not logged, because their addresses would add nothing you need.

```
npx wrangler containers list
npx wrangler tail
```

Lines to look for:

- `restored N objects from storage`: a container started.
- `mirror: storage cannot be reached`: R2 is failing. The game goes on.
- `could not restore the games from storage, so the server will not start`: see below.

## Rolling back

Go back to the commit you want, and deploy it.

```
git checkout <commit>
cd cloudflare && npm ci && npx wrangler deploy
```

`npx wrangler rollback` moves the Worker back, but Cloudflare's documentation does not say that it moves the container image, so a deploy is the safe way. A saved game that does not replay under the older rules is left out, and the log says which one. Its logs stay in R2, so it comes back with the newer version.

## Restoring from R2

This happens by itself each time a container starts. R2 is the only lasting copy, so do not empty the bucket. Each log is under `v1/<table code>.<kind>/`, where the kinds are `db`, `talk`, `clerk` and `seats`. `v1/_spend.ledger/` holds the budget's running total. Each line of an object is one row, as a JSON string.

```
npx wrangler r2 object get charter-logs/v1/ABCDE.db/000000000000-000000000512.jsonl --remote --file ABCDE.jsonl
```

If a log has a gap, the server will not start, so that it does not run with a game missing. The log names the log with the gap. To give up that one game, delete the objects under its prefix and open the address again.

```
npx wrangler r2 object delete charter-logs/v1/ABCDE.db/000000000000-000000000512.jsonl --remote
```

## What it costs

| Item | Cost |
|---|---|
| Workers Paid | $5 a month. It includes 25 GiB-hours of memory, 200 GB-hours of disk and 375 vCPU-minutes. |
| A `basic` container | About 1 cent an hour awake, past what is included. |
| About 40 hours awake in a month | About 15 cents past the included amounts, so about $5 in all. |
| Awake all month, which only constant visitors could cause | About $7 past the included amounts, so about $12 in all. |
| R2, Worker and Durable Object requests | Likely nothing at this size. R2 includes 10 GB, 1 million writes and 10 million reads a month. |
| Claude | Separate. A game of four Claude seats made about 230 requests and cost about $10 at list prices when it was measured. |

Check Cloudflare's current prices before you rely on these.

## The checks

From the top of the repository, with no account:

```
make deploy-check
cd cloudflare && npm ci && npx tsc --noEmit && npx wrangler deploy --dry-run
```

`npx wrangler dev` also runs the real Worker, the container and a local R2 on this computer.

import Tests.Basic

/-- `lake test`: the `#guard` checks run at build time. This exe re-runs the
round trip on a larger generated scene and writes `Tests/golden.gpc`
(the `sample` stream) for the JavaScript decoder test `web/decode.test.mjs`. -/
def main : IO UInt32 := do
  let cmds : List GpuCmd.Cmd := (List.range 2000).map fun i =>
    .draw (i % 5).toUInt32 (GpuCmd.Transform.at i.toFloat 0 (-i.toFloat)) (i * 77).toUInt32 i.toUInt32
  let ok := GpuCmd.decode (GpuCmd.encode (sample ++ cmds)) == some (sample ++ cmds)
  IO.println s!"round trip of {sample.length + cmds.length} commands: {if ok then "ok" else "FAILED"}"
  IO.FS.writeBinFile "Tests/golden.gpc" (GpuCmd.encode sample)
  return if ok then 0 else 1

import GpuCmd

/-! Axiom audit for every theorem listed under README "Guarantees". -/

#print axioms GpuCmd.decode_encode
#print axioms GpuCmd.decodeList_encodeList
#print axioms GpuCmd.readCmd_cmdBytes
#print axioms GpuCmd.readPrim_primBytes
#print axioms GpuCmd.readMotion_motionBytes
#print axioms GpuCmd.Wire.readU32_u32
#print axioms GpuCmd.Wire.readF32_f32
#print axioms GpuCmd.Wire.readUleb_uleb
#print axioms GpuCmd.Wire.readStr_str

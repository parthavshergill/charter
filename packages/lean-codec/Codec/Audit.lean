import Codec

/-! Axiom audit for every theorem listed under README "Guarantees".
Expected: each line mentions at most `propext`, `Quot.sound`, `Classical.choice`. -/

-- Whole-input and ByteArray round trips, canonicity, injectivity
#print axioms Codec.decode_encode
#print axioms Codec.decodeBytes_encodeBytes
#print axioms Codec.encode_decode
#print axioms Codec.encodeBytes_decodeBytes
#print axioms Codec.encode_injective
-- Building blocks
#print axioms Codec.decodeNat_encodeNat
#print axioms Codec.encodeNat_decodeNat
#print axioms Codec.decodeFixed_encodeFixed
#print axioms Codec.decodeFixed_lt
#print axioms Codec.decodeMany_encode
#print axioms Codec.decodeMany_canonical
#print axioms Codec.ofEquiv_lawful
#print axioms Codec.ofEquiv_canonical
#print axioms Codec.ofPartial_lawful
#print axioms Codec.ofPartial_canonical
-- LawfulCodec instances (decode_encode)
#print axioms Codec.lawfulUnit
#print axioms Codec.lawfulBool
#print axioms Codec.lawfulUInt8
#print axioms Codec.lawfulUInt16
#print axioms Codec.lawfulUInt32
#print axioms Codec.lawfulUInt64
#print axioms Codec.lawfulNat
#print axioms Codec.lawfulInt
#print axioms Codec.lawfulFin
#print axioms Codec.lawfulString
#print axioms Codec.lawfulList
#print axioms Codec.lawfulArray
#print axioms Codec.lawfulOption
#print axioms Codec.lawfulProd
#print axioms Codec.lawfulSum
-- CanonicalCodec instances (encode_decode)
#print axioms Codec.canonicalUnit
#print axioms Codec.canonicalBool
#print axioms Codec.canonicalUInt8
#print axioms Codec.canonicalUInt16
#print axioms Codec.canonicalUInt32
#print axioms Codec.canonicalUInt64
#print axioms Codec.canonicalNat
#print axioms Codec.canonicalInt
#print axioms Codec.canonicalFin
#print axioms Codec.canonicalString
#print axioms Codec.canonicalList
#print axioms Codec.canonicalArray
#print axioms Codec.canonicalOption
#print axioms Codec.canonicalProd
#print axioms Codec.canonicalSum

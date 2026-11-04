(specialize reduce Gf64 (condition (= Gf64.BITS 64))
  (let high (field product hi))
  (let overflow (xor (xor (shr64 high 63) (shr64 high 61)) (shr64 high 60)))
  (return (xor (xor (xor (xor (xor (xor (xor (xor (field product lo) high) (shl64 high 1)) (shl64 high 3)) (shl64 high 4)) overflow) (shl64 overflow 1)) (shl64 overflow 3)) (shl64 overflow 4))))

https://github.com/jneem/teddy
packed substring matching: do as little work as possible per 16 bytes

Result.least significant bit (% 8 == pattern idx) (/ 8 = byte offset)

A0 = A & 0xF
A1 = A >> 4

c0 = pshufb A0 B0
c1 = pshufb A1 B1
c = c0 & c1
c ! i  -- bitset giving matching fingerprints for ith byte in the 16byte register

=> lsb of c is the pattern matched,

* 1 byte per fingerprint: good if fingerprints are rare in haystack (to avoid verfication step)

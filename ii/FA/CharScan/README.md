Scanner = MiniScanner | Teddy | FDR

1: Miniprefix: +1 to check bit carries through pattern
2. Teddy: shuffle nybble lookup for n={1,2,3} prefixes of patterns
3. FDR: Byte at a time, check if byte appears at all expected positions for any pattern in set

0. vermicelli: 1-2 chars; size 2 sets differing only at 1 bit (eg: ascii 'a' and 'A')

-- more scans
https://github.com/geofflangdale/scans/tree/master

parsing:
1. cmp against all structural characters, in json: "[]{}:,\"
2. find start/end points of strings, then switch off all structural chars within it
3. start from colon locations, scan backwards and forwards for key/values

blsr, clear lowest set bit : s = s & (s - 1)

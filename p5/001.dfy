// Run-Length Encoding

// This is a compression algorithm that takes a string and compresses it
// by turning a consecutive sequence of the same character into a number (representing
// the count) and the character itself.

// For example:
// Compression: "AAAABBB" -> "4A3B"
// Decompression: "4A3B" -> "AAAABBB"

// This test case tests properties for the decompression part of the algorithm.

datatype Pair = P(val: int, count: nat)

// Decompression: Turn [(A, 2), (B, 1)] back into [A, A, B]
function {:induction false} Decompression(rle: seq<Pair>): seq<int> {
  if |rle| == 0 then []
  else Repeat(rle[0].val, rle[0].count) + Decompression(rle[1..])
}

// Helper: Create a list of 'n' copies of 'x'
function {:induction false} Repeat(x: int, n: nat): seq<int> {
  if n == 0 then [] else [x] + Repeat(x, n-1)
}

// Helper: Count volume of data in compressed form
function {:induction false} TotalCount(rle: seq<Pair>): nat {
  if |rle| == 0 then 0 else rle[0].count + TotalCount(rle[1..])
}

// Proves that decompression preserves the "volume" of data
method {:induction false} Test_Volume(rle: seq<Pair>) {
  assert |Decompression(rle)| == TotalCount(rle) by {
    Prove_Volume(rle);
  }
}

// Proves that we can split a compressed file, decompress the parts,
// and join them, and it works exactly the same as decompressing the whole file
method {:induction false} Test_Parallel_Decompression(a: seq<Pair>, b: seq<Pair>) {
  assert Decompression(a + b) == Decompression(a) + Decompression(b) by {
    Prove_Parallel_Decompression(a, b);
  }
}

/-
Copyright (c) 2025 Drift Systems Inc. Released under Apache 2.0 license.

# Split-Loop Adder: chunked popcount is lossless

Hardware popcount in a parallel split-loop adder tree computes the
population count of a long bit-vector by partitioning it into chunks,
counting each chunk independently, and summing the partial counts.

This file proves the optimization is *lossless*: the chunked total
equals the popcount of the concatenated input.

The result is purely combinatorial — it does not depend on how the
chunks were produced. Any partition into sub-lists whose concatenation
recovers the input yields the same total popcount.
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.List.Count
import Mathlib.Data.Nat.Basic

namespace DriftHardware

/-- Population count of a bit-list: count the `true` bits. -/
def naivePopcount (bits : List Bool) : Nat :=
  bits.countP id

/-- Chunked popcount: sum the per-chunk popcount of a list of chunks. -/
def splitPopcount (chunks : List (List Bool)) : Nat :=
  (chunks.map naivePopcount).sum

/-- Popcount distributes over list concatenation. -/
theorem naivePopcount_append (xs ys : List Bool) :
    naivePopcount (xs ++ ys) = naivePopcount xs + naivePopcount ys := by
  unfold naivePopcount
  exact List.countP_append

/--
**Split-Loop Lossless.**
For any partition of a bit-list into chunks, the sum of per-chunk
popcounts equals the popcount of the flat (concatenated) input.

Structurally certifies the split-loop adder tree introduces no error:
rearranging the work across parallel chunks is algebraically the same
as a single serial scan over the flat input.
-/
theorem split_loop_lossless (chunks : List (List Bool)) :
    splitPopcount chunks = naivePopcount chunks.flatten := by
  unfold splitPopcount naivePopcount
  exact (List.countP_flatten).symm

end DriftHardware

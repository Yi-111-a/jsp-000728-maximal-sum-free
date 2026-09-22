import JSPProblem.BitmaskCount

/-!
# JSP-000728 — exact counts for small `n`

Exact values of `maxSumFreeCount n`, the number of inclusion-maximal
sum-free subsets of `{1, …, n}`, computed by kernel evaluation (`decide`).

The verified values are:

| `n` | `maxSumFreeCount n` | maximal sum-free subsets                          |
|-----|---------------------|---------------------------------------------------|
| 0   | 1                   | `∅`                                               |
| 1   | 1                   | `{1}`                                             |
| 2   | 2                   | `{1}`, `{2}`                                      |
| 3   | 2                   | `{1,3}`, `{2,3}`                                  |
| 4   | 4                   | `{1,3}`, `{1,4}`, `{2,3}`, `{3,4}`                |
| 5   | 5                   | `{1,4}`, `{2,3}`, `{2,5}`, `{1,3,5}`, `{3,4,5}`   |

For larger `n` the explicit sets are omitted for brevity; the verified
counts are:

| `n` | `maxSumFreeCount n` |
|-----|---------------------|
| 6   | 6                   |
| 7   | 8                   |
| 8   | 13                  |
| 9   | 17                  |
| 10  | 23                  |
| 11  | 29                  |
| 12  | 37                  |

For `n ≤ 8` the counts are verified by direct kernel `decide` on the
finset enumeration; for `9 ≤ n ≤ 12` they are verified via the bitmask
bridge `maxSumFreeCount_eq_maskCount` (`BitmaskCount.lean`), which keeps
kernel evaluation memory-feasible (plain `decide` on the powerset
enumeration exhausts memory for `n ≥ 11`).  These values agree with the
OEIS/folklore sequence of maximal sum-free subset counts.

Note: `{2,3}` is maximal in `{1,…,4}` (inserting `1` gives `1+1=2 ∈`,
inserting `4` gives `2+2=4 ∈`), so `f(4) = 4`.
-/

namespace JSP000728

theorem count_zero : maxSumFreeCount 0 = 1 := by decide

theorem count_one : maxSumFreeCount 1 = 1 := by decide

theorem count_two : maxSumFreeCount 2 = 2 := by decide

theorem count_three : maxSumFreeCount 3 = 2 := by decide

theorem count_four : maxSumFreeCount 4 = 4 := by decide

theorem count_five : maxSumFreeCount 5 = 5 := by decide

theorem count_six : maxSumFreeCount 6 = 6 := by decide

theorem count_seven : maxSumFreeCount 7 = 8 := by decide

theorem count_eight : maxSumFreeCount 8 = 13 := by decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem count_nine : maxSumFreeCount 9 = 17 := by
  rw [maxSumFreeCount_eq_maskCount]; decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem count_ten : maxSumFreeCount 10 = 23 := by
  rw [maxSumFreeCount_eq_maskCount]; decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem count_eleven : maxSumFreeCount 11 = 29 := by
  rw [maxSumFreeCount_eq_maskCount]; decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem count_twelve : maxSumFreeCount 12 = 37 := by
  rw [maxSumFreeCount_eq_maskCount]; decide

end JSP000728

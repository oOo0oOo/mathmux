module

import MathmuxFixture.Shared

namespace MathmuxFixture.Worker4

open MathmuxFixture

example : rowland 3 = 10 := by
  norm_num [rowland]

example : rowland 4 = 15 := by
  norm_num [rowland]

example : rowland 5 = 18 := by
  norm_num [rowland]

example : rowland 6 = 19 := by
  norm_num [rowland]

example : increment 3 = 5 := by
  norm_num [increment, rowland]

example : increment 4 = 3 := by
  norm_num [increment, rowland]

example (n : ℕ) : 0 < Nat.gcd (n + 2) (rowland n) := by
  exact increment_pos n

example (n : ℕ) : rowland n + 1 ≤ rowland (n + 1) := by
  rw [rowland_succ_eq]
  exact Nat.add_le_add_left (increment_pos n) (rowland n)

theorem benchmarkTarget (n : ℕ) : n + 44 = 44 + n := by
  omega

end MathmuxFixture.Worker4

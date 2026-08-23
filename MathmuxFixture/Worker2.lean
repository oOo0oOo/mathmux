import MathmuxFixture.Shared

namespace MathmuxFixture.Worker2

open MathmuxFixture

example : rowland 1 = 8 := by
  norm_num [rowland]

example : rowland 2 = 9 := by
  norm_num [rowland]

example : rowland 3 = 10 := by
  norm_num [rowland]

example : rowland 4 = 15 := by
  norm_num [rowland]

example : increment 1 = 1 := by
  norm_num [increment, rowland]

example : increment 2 = 1 := by
  norm_num [increment, rowland]

example (n : ℕ) : increment n ∣ n + 2 := by
  exact increment_dvd_index n

example (n : ℕ) : rowland n < rowland (n + 1) := by
  rw [rowland_succ_eq]
  exact Nat.lt_add_of_pos_right (increment_pos n)

theorem benchmarkTarget (n : ℕ) : n + 22 = 22 + n := by
  omega

end MathmuxFixture.Worker2

import MathmuxFixture.Shared

namespace MathmuxFixture.Worker3

open MathmuxFixture

example : rowland 2 = 9 := by
  norm_num [rowland]

example : rowland 3 = 10 := by
  norm_num [rowland]

example : rowland 4 = 15 := by
  norm_num [rowland]

example : rowland 5 = 18 := by
  norm_num [rowland]

example : increment 2 = 1 := by
  norm_num [increment, rowland]

example : increment 3 = 5 := by
  norm_num [increment, rowland]

example (n : ℕ) : increment n ∣ rowland n := by
  exact increment_dvd_value n

example (n : ℕ) : rowland (n + 1) ≠ rowland n := by
  rw [rowland_succ_eq]
  exact (Nat.lt_add_of_pos_right (increment_pos n)).ne'

theorem benchmarkTarget (n : ℕ) : n + 33 = 33 + n := by
  omega

end MathmuxFixture.Worker3

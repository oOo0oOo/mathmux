import MathmuxFixture.Shared

namespace MathmuxFixture.Worker1

open MathmuxFixture

example : rowland 0 = 7 := by
  rfl

example : rowland 1 = 8 := by
  norm_num [rowland]

example : rowland 2 = 9 := by
  norm_num [rowland]

example : rowland 3 = 10 := by
  norm_num [rowland]

example : increment 0 = 1 := by
  norm_num [increment, rowland]

example : increment 1 = 1 := by
  norm_num [increment, rowland]

example (n : ℕ) : increment n ≤ n + 2 := by
  exact Nat.le_of_dvd (by omega) (increment_dvd_index n)

example (n : ℕ) : rowland (n + 1) ≥ rowland n := by
  simp only [rowland_succ_eq]
  omega

theorem benchmarkTarget (n : ℕ) : n + 11 = 11 + n := by
  omega

end MathmuxFixture.Worker1

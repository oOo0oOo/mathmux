module

public import Mathlib

namespace MathmuxFixture

@[expose] public section

/-- Rowland's recurrence, indexed from zero so `rowland 0 = a(1)`. -/
def rowland : ℕ → ℕ
  | 0 => 7
  | n + 1 => rowland n + Nat.gcd (n + 2) (rowland n)

@[simp]
theorem rowland_zero : rowland 0 = 7 := rfl

@[simp]
theorem rowland_succ (n : ℕ) :
    rowland (n + 1) = rowland n + Nat.gcd (n + 2) (rowland n) := rfl

def increment (n : ℕ) : ℕ := Nat.gcd (n + 2) (rowland n)

theorem rowland_succ_eq (n : ℕ) : rowland (n + 1) = rowland n + increment n := by
  rfl

theorem increment_dvd_index (n : ℕ) : increment n ∣ n + 2 := by
  exact Nat.gcd_dvd_left _ _

theorem increment_dvd_value (n : ℕ) : increment n ∣ rowland n := by
  exact Nat.gcd_dvd_right _ _

theorem increment_pos (n : ℕ) : 0 < increment n := by
  exact Nat.gcd_pos_of_pos_left _ (by omega)

end

end MathmuxFixture

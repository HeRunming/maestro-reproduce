import Mathlib

example (n : ℕ) : n + 0 = n := by simp
example (a b : ℤ) : (a + b)^2 = a^2 + 2*a*b + b^2 := by ring
example : (12 : ℕ) * 12 = 144 := by norm_num

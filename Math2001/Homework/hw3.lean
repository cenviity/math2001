/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic

math2001_init

namespace Nat

/-! # Homework 3

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-3,
for clearer statements and any special instructions. -/

theorem problem1 {a b : ℚ} (h : a = 3 - b) : a + b = 3 ∨ a + b = 4 := by
  sorry

theorem problem2 {t : ℚ} (h : t ^ 2 + t - 6 = 0) : t = 2 ∨ t = -3 := by
  sorry

theorem problem3 : ∃ a b : ℕ, a ≠ 0 ∧ 2 ^ a = 5 * b + 1 := by
  sorry

theorem problem4 (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  sorry

theorem problem5 {x : ℕ} (hx : Odd x) : Odd (x ^ 3) := by
  sorry

theorem problem6 (n : ℕ) : ∃ m ≥ n, Odd m := by
  sorry

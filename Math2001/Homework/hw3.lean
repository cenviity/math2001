/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic

math2001_init

namespace Nat

/-! # Homework 3

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-3,
for clearer statements and any special instructions. -/

theorem problem1 {a b : ℚ} (h : a = 3 - b) : a + b = 3 ∨ a + b = 4 := by
  left
  addarith [h]

theorem problem2 {t : ℚ} (h : t ^ 2 + t - 6 = 0) : t = 2 ∨ t = -3 := by
  have h' :=
    calc (t - 2) * (t + 3)
      _ = t ^ 2 + t - 6 := by ring
      _ = 0 := by rw [h]
  obtain h1 | h2 := eq_zero_or_eq_zero_of_mul_eq_zero h'
  · left
    addarith [h1]
  · right
    addarith [h2]

theorem problem3 : ∃ a b : ℕ, a ≠ 0 ∧ 2 ^ a = 5 * b + 1 := by
  use 4, 3
  constructor
  · numbers
  · numbers

theorem problem4 (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  by_cases h : x ≥ 0
  · use x + 1
    calc (x + 1) ^ 2
      _ = x + (x ^ 2 + x + 1) := by ring
      _ > x := by extra
  · push_neg at h
    have h' : -(3 * x) > 0 := by addarith [h]
    use x - 1
    calc (x - 1) ^ 2
      _ = x + (-(3 * x)) + (x ^ 2 + 1) := by ring
      _ > x + (-(3 * x)) := by extra
      _ > x := by extra

theorem problem5 {x : ℕ} (hx : Odd x) : Odd (x ^ 3) := by
  dsimp [Odd] at *
  obtain ⟨k, hk⟩ := hx
  use 4 * k ^ 3 + 6 * k ^ 2 + 3 * k
  calc x ^ 3
    _ = (2 * k + 1) ^ 3 := by rw [hk]
    _ = 2 * (4 * k ^ 3 + 6 * k ^ 2 + 3 * k) + 1 := by ring

theorem problem6 (n : ℕ) : ∃ m ≥ n, Odd m := by
  use 2 * n + 1
  constructor
  · calc 2 * n + 1
      _ = n + (n + 1) := by ring
      _ ≥ n := by extra
  · use n
    ring

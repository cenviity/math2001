/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {a : ℚ} (h : ∃ b : ℚ, a = b ^ 2 + 1) : a > 0 := by
  obtain ⟨b, hb⟩ := h
  calc
    a = b ^ 2 + 1 := hb
    _ > 0 := by extra


example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  obtain ⟨x, hxt⟩ := h
  obtain hx | hx := le_or_gt x 0
  · have hxt' : 0 < (-x) * t := by addarith [hxt]
    have hx' : 0 ≤ -x := by addarith [hx]
    cancel -x at hxt'
    apply ne_of_gt hxt'
  · have hxt' :=
      calc
        0 < -(x * t) := by addarith [hxt]
        _ = x * -t := by ring
    cancel x at hxt'
    apply ne_of_lt
    addarith [hxt']

example : ∃ n : ℤ, 12 * n = 84 := by
  use 7
  numbers


example (x : ℝ) : ∃ y : ℝ, y > x := by
  use x + 1
  extra


example : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 11 := by
  use 6, 5
  numbers

example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use a + 1, a
  ring

example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p + q) / 2
  constructor
  · calc
      p = (p + p) / 2 := by ring
      _ < (p + q) / 2 := by rel [h]
  · calc
      q = (q + q) / 2 := by ring
      _ > (p + q) / 2 := by rel [h]

example : ∃ a b c d : ℕ,
    a ^ 3 + b ^ 3 = 1729 ∧ c ^ 3 + d ^ 3 = 1729 ∧ a ≠ c ∧ a ≠ d := by
  use 1, 12, 9, 10
  constructor
  numbers
  constructor
  numbers
  constructor
  numbers
  numbers

/-! # Exercises -/


example : ∃ t : ℚ, t ^ 2 = 1.69 := by
  use 1.3
  numbers

example : ∃ m n : ℤ, m ^ 2 + n ^ 2 = 85 := by
  use 9, 2
  numbers

example : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by
  use -0.5
  constructor
  · numbers
  · numbers

example : ∃ a b : ℕ, 2 ^ a = 5 * b + 1 := by
  use 4, 3
  numbers

example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  obtain hx | hx := le_or_gt x 0
  · have hx' : -x ≥ 0 := by addarith [hx]
    use x - 1 / 2
    calc (x - 1 / 2) ^ 2
      _ = x ^ 2 - x + 1 / 4 := by ring
      _ ≥ -x + 1 / 4 := by extra
      _ ≥ 0 + 1 / 4 := by rel [hx']
      _ > 0 := by numbers
      _ ≥ x := by rel [hx]
  · use x + 1 / 2
    calc (x + 1 / 2) ^ 2
      _ = x ^ 2 + x + 1 / 4 := by ring
      _ > x + 1 / 4 := by extra
      _ > x := by extra

/- TODO: Use `le_or_gt` to prove this. -/
example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  obtain ⟨a, hat⟩ := h
  have hat' :=
    calc (a - 1) * (t - 1)
      _ = a * t + 1 - a - t := by ring
      _ < a + t - a - t := by rel [hat]
      _ = 0 := by ring
  apply ne_of_lt at hat'
  apply mul_ne_zero_iff.mp at hat'
  obtain ⟨-, ht⟩ := hat'
  apply sub_ne_zero.mp ht

example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  obtain ⟨a, ham⟩ := h
  have ham' : m = 2 * a := by rw [ham]
  obtain ha | ha := le_or_succ_le a 2
  · apply ne_of_lt
    calc
      m = 2 * a := ham'
      _ ≤ 2 * 2 := by rel [ha]
      _ < 5 := by numbers
  · apply ne_of_gt
    calc
      m = 2 * a := ham'
      _ ≥ 2 * 3 := by rel [ha]
      _ > 5 := by numbers

example {n : ℤ} : ∃ a, 2 * a ^ 3 ≥ n * a + 7 := by
  obtain h | h := le_or_gt n 0
  · use 2
    calc n * 2 + 7
      _ ≤ 0 * 2 + 7 := by rel [h]
      _ ≤ 2 * 2 ^ 3 := by numbers
  · use n + 2
    calc 2 * (n + 2) ^ 3
      _ = 2 * n ^ 3 + 12 * n ^ 2 + 24 * n + 16 := by ring
      _ ≥ 2 * 0 ^ 3 + 12 * n ^ 2 + 24 * n + 16 := by rel [h]
      _ = (11 * n ^ 2 + 22 * n + 9) + n ^ 2 + 2 * n + 7 := by ring
      _ ≥ n ^ 2 + 2 * n + 7 := by extra
      _ = n * (n + 2) + 7 := by ring

example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by
  use
    (b + c - a) / 2,
    (a + c - b) / 2,
    (a + b - c) / 2
  constructor
  · calc (b + c - a) / 2
      _ ≥ (a - a) / 2 := by rel [ha]
      _ = 0 := by ring
  constructor
  · calc (a + c - b) / 2
      _ ≥ (b - b) / 2 := by rel [hb]
      _ = 0 := by ring
  constructor
  · calc (a + b - c) / 2
      _ ≥ (c - c) / 2 := by rel [hc]
      _ = 0 := by ring
  constructor
  · ring
  constructor
  · ring
  · ring

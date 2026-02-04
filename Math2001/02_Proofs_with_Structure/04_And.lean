/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {x y : ℤ} (h : 2 * x - y = 4 ∧ y - x + 1 = 2) : x = 5 := by
  obtain ⟨h1, h2⟩ := h
  calc
    x = 2 * x - y + (y - x + 1) - 1 := by ring
    _ = 4 + 2 - 1 := by rw [h1, h2]
    _ = 5 := by ring


example {p : ℚ} (hp : p ^ 2 ≤ 8) : p ≥ -5 := by
  have hp' : -3 ≤ p ∧ p ≤ 3
  · apply abs_le_of_sq_le_sq'
    calc p ^ 2
      _ ≤ 9 := by addarith [hp]
      _ = 3 ^ 2 := by numbers
    numbers
  obtain ⟨h, -⟩ := hp'
  addarith [h]

example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 ∧ b = 1 := by
  constructor
  · calc
      a = 4 + 5 * b := by addarith [h1]
      _ = -6 + 5 * (b + 2) := by ring
      _ = -6 + 5 * 3 := by rw [h2]
      _ = 9 := by ring
  · addarith [h2]


example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 ∧ b = 1 := by
  have hb : b = 1 := by addarith [h2]
  constructor
  · calc
      a = 4 + 5 * b := by addarith [h1]
      _ = 4 + 5 * 1 := by rw [hb]
      _ = 9 := by ring
  · apply hb


example {a b : ℝ} (h1 : a ^ 2 + b ^ 2 = 0) : a = 0 ∧ b = 0 := by
  have h2 : a ^ 2 = 0
  · apply le_antisymm
    calc a ^ 2
      _ ≤ a ^ 2 + b ^ 2 := by extra
      _ = 0 := h1
    extra
  cancel 2 at h2
  constructor
  · apply h2
  · have h3 :=
      calc b ^ 2
        _ = 0 ^ 2 + b ^ 2 := by ring
        _ = a ^ 2 + b ^ 2 := by rw [h2]
        _ = 0 := h1
    cancel 2 at h3

/-! # Exercises -/


example {a b : ℚ} (H : a ≤ 1 ∧ a + b ≤ 3) : 2 * a + b ≤ 4 := by
  obtain ⟨h1, h2⟩ := H
  calc 2 * a + b
    _ = a + (a + b) := by ring
    _ ≤ 1 + 3 := by rel [h1, h2]
    _ = 4 := by numbers

example {r s : ℝ} (H : r + s ≤ 1 ∧ r - s ≤ 5) : 2 * r ≤ 6 := by
  obtain ⟨h1, h2⟩ := H
  calc 2 * r
    _ = (r + s) + (r - s) := by ring
    _ ≤ 1 + 5 := by rel [h1, h2]
    _ = 6 := by numbers

example {m n : ℤ} (H : n ≤ 8 ∧ m + 5 ≤ n) : m ≤ 3 := by
  obtain ⟨h1, h2⟩ := H
  calc
    m = m + 5 - 5 := by ring
    _ ≤ n - 5 := by rel [h2]
    _ ≤ 8 - 5 := by rel [h1]
    _ ≤ 3 := by numbers

example {p : ℤ} (hp : p + 2 ≥ 9) : p ^ 2 ≥ 49 ∧ 7 ≤ p := by
  have hp' : p ≥ 7 := by addarith [hp]
  constructor
  · calc p ^ 2
      _ ≥ 7 ^ 2 := by rel [hp']
      _ = 49 := by numbers
  · apply hp'

example {a : ℚ} (h : a - 1 ≥ 5) : a ≥ 6 ∧ 3 * a ≥ 10 := by
  have ha : a ≥ 6 := by addarith [h]
  constructor
  · apply ha
  · calc 3 * a
      _ ≥ 3 * 6 := by rel [ha]
      _ ≥ 10 := by numbers

example {x y : ℚ} (h : x + y = 5 ∧ x + 2 * y = 7) : x = 3 ∧ y = 2 := by
  obtain ⟨h1, h2⟩ := h
  have hy :=
    calc
      y = (x + 2 * y) - (x + y) := by ring
      _ = 7 - 5 := by rw [h1, h2]
      _ = 2 := by ring
  constructor
  · calc
      x = 5 - y := by addarith [h1]
      _ = 5 - 2 := by rw [hy]
      _ = 3 := by ring
  · apply hy

example {a b : ℝ} (h1 : a * b = a) (h2 : a * b = b) :
    a = 0 ∧ b = 0 ∨ a = 1 ∧ b = 1 := by
  have h1' :=
    calc a * (b - 1)
      _ = a * b - a := by ring
      _ = a - a := by rw [h1]
      _ = 0 := by ring
  apply eq_zero_or_eq_zero_of_mul_eq_zero at h1'
  have hab :=
    calc
      a = a * b := by addarith [h1]
      _ = b := h2
  obtain h | h := h1'
  · left
    constructor
    · apply h
    · calc
        b = a := by addarith [hab]
        _ = 0 := h
  · right
    constructor
    · calc
        a = b := hab
        _ = 1 := by addarith [h]
    · addarith [h]

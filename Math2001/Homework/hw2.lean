/- Copyright (c) Heather Macbeth, 2024.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-! # Homework 2

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-2,
for clearer statements and any special instructions. -/


theorem problem1 {x : ℚ} (h1 : x ^ 2 = 9) (h2 : 1 < x) : x = 3 := by
  have :=
    calc x * (x + 3)
      _ = x ^ 2 + 3 * x := by ring
      _ = 9 + 3 * x := by rw [h1]
      _ = 3 * (x + 3) := by ring
  cancel x + 3 at this

theorem problem2 {s : ℚ} (h1 : 3 * s ≤ -15) (h2 : 2 * s ≥ -10) : s = -5 := by
  have h1' :=
    calc
      s = 3 * s / 3 := by ring
      _ ≤ -15 / 3 := by rel [h1]
      _ = -5 := by numbers
  have h2' :=
    calc
      s = 2 * s / 2 := by ring
      _ ≥ -10 / 2 := by rel [h2]
      _ = -5 := by numbers
  apply le_antisymm h1' h2'

theorem problem3 {t : ℚ} (h : t = 2 ∨ t = -3) : t ^ 2 + t - 6 = 0 := by
  obtain h | h := h
  · rw [h]
    numbers
  · rw [h]
    numbers

theorem problem4 {x : ℤ} : 3 * x ≠ 10 := by
  obtain hx | hx : x ≤ 3 ∨ 4 ≤ x := le_or_succ_le x 3
  · apply ne_of_lt
    calc 3 * x
      _ ≤ 3 * 3 := by rel [hx]
      _ < 10 := by numbers
  · apply ne_of_gt
    calc 3 * x
      _ ≥ 3 * 4 := by rel [hx]
      _ > 10 := by numbers

theorem problem5 {x y : ℝ} (h1 : 2 ≤ x ∨ 2 ≤ y) (h2 : x ^ 2 + y ^ 2 = 4) :
    x ^ 2 * y ^ 2 = 0 := by
  obtain hx | hy := h1
  · have hx1 :=
      calc x ^ 2
        _ = x ^ 2 + y ^ 2 - y ^ 2 := by ring
        _ = 4 - y ^ 2 := by rw [h2]
        _ ≤ 4 - y ^ 2 + y ^ 2 := by extra
        _ = 4 := by ring
    have hx2 :=
      calc x ^ 2
        _ ≥ 2 ^ 2 := by rel [hx]
        _ = 4 := by numbers
    have hx3 : x ^ 2 = 4 := le_antisymm hx1 hx2
    have hy :=
      calc y ^ 2
        _ = x ^ 2 + y ^ 2 - x ^ 2 := by ring
        _ = 4 - 4 := by rw [h2, hx3]
        _ = 0 := by numbers
    rw [hx3, hy]
    numbers
  · have hy1 :=
      calc y ^ 2
        _ = x ^ 2 + y ^ 2 - x ^ 2 := by ring
        _ = 4 - x ^ 2 := by rw [h2]
        _ ≤ 4 - x ^ 2 + x ^ 2 := by extra
        _ = 4 := by ring
    have hy2 :=
      calc y ^ 2
        _ ≥ 2 ^ 2 := by rel [hy]
        _ = 4 := by numbers
    have hy3 : y ^ 2 = 4 := le_antisymm hy1 hy2
    have hx :=
      calc x ^ 2
        _ = x ^ 2 + y ^ 2 - y ^ 2 := by ring
        _ = 4 - 4 := by rw [h2, hy3]
        _ = 0 := by numbers
    rw [hx, hy3]
    numbers

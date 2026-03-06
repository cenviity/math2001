/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic
import Library.Theory.ModEq.Defs

math2001_init

namespace Int

/-! # Homework 4

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-4,
for clearer statements and any special instructions. -/

theorem problem1 (n : ℤ) : Odd (3 * n ^ 2 + 3 * n - 1) := by
  by_cases h : Odd n
  · obtain ⟨k, hk⟩ := h
    use 6 * k ^ 2 + 9 * k + 2
    calc 3 * n ^ 2 + 3 * n - 1
      _ = 3 * (2 * k + 1) ^ 2 + 3 * (2 * k + 1) - 1 := by rw [hk]
      _ = 2 * (6 * k ^ 2 + 9 * k + 2) + 1 := by ring
  · apply (even_iff_not_odd n).2 at h
    obtain ⟨k, hk⟩ := h
    use 6 * k ^ 2 + 3 * k - 1
    calc 3 * n ^ 2 + 3 * n - 1
      _ = 3 * (2 * k) ^ 2 + 3 * (2 * k) - 1 := by rw [hk]
      _ = 2 * (6 * k ^ 2 + 3 * k - 1) + 1 := by ring

theorem problem2 : (8 : ℤ) ∣ 96 := by
  use 12
  numbers

theorem problem3 : ¬(8 : ℤ) ∣ -55 := by
  apply not_dvd_of_exists_lt_and_lt
  use -7
  constructor <;> numbers

theorem problem4 {a b c : ℤ} (hab : a ^ 3 ∣ b) (hbc : b ^ 2 ∣ c) : a ^ 6 ∣ c := by
  obtain ⟨x, hx⟩ := hab
  obtain ⟨y, hy⟩ := hbc
  use x ^ 2 * y
  calc
    c = b ^ 2 * y := hy
    _ = (a ^ 3 * x) ^ 2 * y := by rw [hx]
    _ = a ^ 6 * x ^ 2 * y := by ring

theorem problem5 : 31 ≡ 13 [ZMOD 3] := by
  use 6
  numbers

theorem problem6 : ¬ 51 ≡ 62 [ZMOD 5] := by
  dsimp [ModEq]
  apply not_dvd_of_exists_lt_and_lt
  use -3
  constructor <;> numbers

theorem problem7 (h : a ≡ b [ZMOD n]) : a ^ 3 ≡ b ^ 3 [ZMOD n] := by
  obtain ⟨x, hx⟩ := h
  use x * (a ^ 2 + a * b + b ^ 2)
  calc a ^ 3 - b ^ 3
    _ = (a - b) * (a ^ 2 + a * b + b ^ 2) := by ring
    _ = n * x * (a ^ 2 + a * b + b ^ 2) := by rw [hx]
    _ = n * (x * (a ^ 2 + a * b + b ^ 2)) := by ring

theorem problem8 (h1 : a ≡ b [ZMOD n]) (h2 : b ≡ c [ZMOD n]) : a ≡ c [ZMOD n] := by
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use x + y
  calc a - c
    _ = a - b + (b - c) := by ring
    _ = n * x + n * y := by rw [hx, hy]
    _ = n * (x + y) := by ring

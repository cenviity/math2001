/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init

namespace Int


example {a : ℚ} : 3 * a + 1 ≤ 7 ↔ a ≤ 2 := by
  constructor
  · intro h
    calc a = ((3 * a + 1) - 1) / 3 := by ring
      _ ≤ (7 - 1) / 3 := by rel [h]
      _ = 2 := by numbers
  · intro h
    calc 3 * a + 1 ≤ 3 * 2 + 1 := by rel [h]
      _ = 7 := by numbers


example {n : ℤ} : 8 ∣ 5 * n ↔ 8 ∣ n := by
  constructor
  · intro ⟨a, ha⟩
    use -3 * a + 2 * n
    calc
      n = -3 * (5 * n) + 16 * n := by ring
      _ = -3 * (8 * a) + 16 * n := by rw [ha]
      _ = 8 * (-3 * a + 2 * n) := by ring
  · intro ⟨a, ha⟩
    use 5 * a
    calc 5 * n = 5 * (8 * a) := by rw [ha]
      _ = 8 * (5 * a) := by ring


theorem odd_iff_modEq (n : ℤ) : Odd n ↔ n ≡ 1 [ZMOD 2] := by
  constructor
  · intro ⟨k, hk⟩
    dsimp [Int.ModEq]
    dsimp [(· ∣ ·)]
    use k
    addarith [hk]
  · intro ⟨k, hk⟩
    use k
    addarith [hk]

theorem even_iff_modEq (n : ℤ) : Even n ↔ n ≡ 0 [ZMOD 2] := by
  constructor
  · intro ⟨k, hk⟩
    dsimp [Int.ModEq]
    dsimp [(· ∣ ·)]
    use k
    addarith [hk]
  · intro ⟨k, hk⟩
    use k
    addarith [hk]

example {x : ℝ} : x ^ 2 + x - 6 = 0 ↔ x = -3 ∨ x = 2 := by
  constructor
  · intro hx
    have h1 :=
      calc (x + 3) * (x - 2)
        _ = x ^ 2 + x - 6 := by ring
        _ = 0 := hx
    obtain h | h := eq_zero_or_eq_zero_of_mul_eq_zero h1
    · left
      addarith [h]
    · right
      addarith [h]
  · intro hx
    obtain h | h := hx
    · calc x ^ 2 + x - 6
        _ = (-3) ^ 2 + (-3) - 6 := by rw [h]
        _ = 0 := by ring
    · calc x ^ 2 + x - 6
        _ = 2 ^ 2 + 2 - 6 := by rw [h]
        _ = 0 := by ring

example {a : ℤ} : a ^ 2 - 5 * a + 5 ≤ -1 ↔ a = 2 ∨ a = 3 := by
  constructor
  · intro ha
    have h :=
      calc (2 * a - 5) ^ 2
        _ = 4 * (a ^ 2 - 5 * a + 5) + 5 := by ring
        _ ≤ 4 * -1 + 5 := by rel [ha]
        _ = 1 ^ 2 := by ring
    obtain ⟨h1, h2⟩ := abs_le_of_sq_le_sq' h (by numbers)
    have h1' :=
      calc 2 * a
        _ = 2 * a - 5 + 5 := by ring
        _ ≥ -1 + 5 := by rel [h1]
        _ = 2 * 2 := by numbers
    cancel 2 at h1'
    have h2' :=
      calc 2 * a
        _ = 2 * a - 5 + 5 := by ring
        _ ≤ 1 + 5 := by rel [h2]
        _ = 2 * 3 := by numbers
    cancel 2 at h2'
    interval_cases a
    · left
      numbers
    · right
      numbers
  · intro ha
    obtain h | h := ha
    · calc a ^ 2 - 5 * a + 5
        _ = 2 ^ 2 - 5 * 2 + 5 := by rw [h]
        _ ≤ -1 := by numbers
    · calc a ^ 2 - 5 * a + 5
        _ = 3 ^ 2 - 5 * 3 + 5 := by rw [h]
        _ ≤ -1 := by numbers

example {n : ℤ} (hn : n ^ 2 - 10 * n + 24 = 0) : Even n := by
  have hn1 :=
    calc (n - 4) * (n - 6)
      _ = n ^ 2 - 10 * n + 24 := by ring
      _ = 0 := hn
  obtain h | h := eq_zero_or_eq_zero_of_mul_eq_zero hn1
  · use 2
    calc
      n = n - 4 + 4 := by ring
      _ = 0 + 4 := by rw [h]
  · use 3
    calc
      n = n - 6 + 6 := by ring
      _ = 0 + 6 := by rw [h]

example {n : ℤ} (hn : n ^ 2 - 10 * n + 24 = 0) : Even n := by
  have hn1 :=
    calc (n - 4) * (n - 6)
      _ = n ^ 2 - 10 * n + 24 := by ring
      _ = 0 := hn
  rw [mul_eq_zero] at hn1 -- `hn1 : n - 4 = 0 ∨ n - 6 = 0`
  obtain h | h := hn1
  · use 2
    calc
      n = n - 4 + 4 := by ring
      _ = 0 + 4 := by rw [h]
  · use 3
    calc
      n = n - 6 + 6 := by ring
      _ = 0 + 6 := by rw [h]

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x + y + 1) := by
  rw [Int.odd_iff_modEq] at *
  calc x + y + 1 ≡ 1 + 1 + 1 [ZMOD 2] := by rel [hx, hy]
    _ = 2 * 1 + 1 := by ring
    _ ≡ 1 [ZMOD 2] := by extra


example (n : ℤ) : Even n ∨ Odd n := by
  mod_cases hn : n % 2
  · left
    rw [Int.even_iff_modEq]
    apply hn
  · right
    rw [Int.odd_iff_modEq]
    apply hn

/-! # Exercises -/


example {x : ℝ} : 2 * x - 1 = 11 ↔ x = 6 := by
  constructor
  · intro hx
    calc
      x = (2 * x - 1 + 1) / 2 := by ring
      _ = (11 + 1) / 2 := by rw [hx]
      _ = 6 := by numbers
  · intro hx
    calc 2 * x - 1
      _ = 2 * 6 - 1 := by rw [hx]
      _ = 11 := by numbers

example {n : ℤ} : 63 ∣ n ↔ 7 ∣ n ∧ 9 ∣ n := by
  constructor
  · intro ⟨k, hk⟩
    constructor
    · use 9 * k
      calc
        n = 63 * k := hk
        _ = 7 * (9 * k) := by ring
    · use 7 * k
      calc
        n = 63 * k := hk
        _ = 9 * (7 * k) := by ring
  · intro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    use 4 * y - 3 * x
    calc
      n = 28 * n - 27 * n := by ring
      _ = 28 * (9 * y) - 27 * n := by rw [hy]
      _ = 28 * (9 * y) - 27 * (7 * x) := by rw [hx]
      _ = 63 * (4 * y - 3 * x) := by ring

theorem dvd_iff_modEq {a n : ℤ} : n ∣ a ↔ a ≡ 0 [ZMOD n] := by
  constructor
  · intro ⟨k, hk⟩
    use k
    addarith [hk]
  · intro ⟨k, hk⟩
    use k
    addarith [hk]

example {a b : ℤ} (hab : a ∣ b) : a ∣ 2 * b ^ 3 - b ^ 2 + 3 * b := by
  rw [dvd_iff_modEq] at *
  calc 2 * b ^ 3 - b ^ 2 + 3 * b
    _ ≡ 2 * 0 ^ 3 - 0 ^ 2 + 3 * 0 [ZMOD a] := by rel [hab]
    _ = 0 := by numbers
    _ ≡ 0 [ZMOD a] := by extra

example {k : ℕ} : k ^ 2 ≤ 6 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by
  constructor
  · intro hk
    have hk' :=
      calc k ^ 2
        _ ≤ 6 := hk
        _ < 3 ^ 2 := by numbers
    cancel 2 at hk'
    interval_cases k
    · left
      numbers
    · right
      left
      numbers
    · right
      right
      numbers
  · intro hk
    obtain h | h | h := hk
    · calc k ^ 2
        _ = 0 ^ 2 := by rw [h]
        _ ≤ 6 := by numbers
    · calc k ^ 2
        _ = 1 ^ 2 := by rw [h]
        _ ≤ 6 := by numbers
    · calc k ^ 2
        _ = 2 ^ 2 := by rw [h]
        _ ≤ 6 := by numbers

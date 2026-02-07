/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init


example {y : ℝ} (x : ℝ) (h : 0 < x * y) (hx : 0 ≤ x) : 0 < y := by
  obtain hneg | hpos : y ≤ 0 ∨ 0 < y := le_or_lt y 0
  · -- the case `y ≤ 0`
    have : ¬0 < x * y
    · apply not_lt_of_ge
      calc
        0 = x * 0 := by ring
        _ ≥ x * y := by rel [hneg]
    contradiction
  · -- the case `0 < y`
    apply hpos


example {t : ℤ} (h2 : t < 3) (h : t - 1 = 6) : t = 13 := by
  have H :=
  calc
    7 = t := by addarith [h]
    _ < 3 := h2
  have : ¬(7 : ℤ) < 3 := by numbers
  contradiction


example {t : ℤ} (h2 : t < 3) (h : t - 1 = 6) : t = 13 := by
  have H :=
  calc
    7 = t := by addarith [h]
    _ < 3 := h2
  numbers at H -- this is a contradiction!


example (n : ℤ) (hn : n ^ 2 + n + 1 ≡ 1 [ZMOD 3]) :
    n ≡ 0 [ZMOD 3] ∨ n ≡ 2 [ZMOD 3] := by
  mod_cases h : n % 3
  · -- case 1: `n ≡ 0 [ZMOD 3]`
    left
    apply h
  · -- case 2: `n ≡ 1 [ZMOD 3]`
    have H :=
      calc 0 ≡ 0 + 3 * 1 [ZMOD 3] := by extra
      _ = 1 ^ 2 + 1 + 1 := by numbers
      _ ≡ n ^ 2 + n + 1 [ZMOD 3] := by rel [h]
      _ ≡ 1 [ZMOD 3] := hn
    numbers at H -- contradiction!
  · -- case 3: `n ≡ 2 [ZMOD 3]`
    right
    apply h


example {p : ℕ} (hp : 2 ≤ p) (H : ∀ m : ℕ, 1 < m → m < p → ¬m ∣ p) : Prime p := by
  constructor
  · apply hp -- show that `2 ≤ p`
  intro m hmp
  have hp' : 0 < p := by extra
  have h1m : 1 ≤ m := Nat.pos_of_dvd_of_pos hmp hp'
  obtain hm | hm_left : 1 = m ∨ 1 < m := eq_or_lt_of_le h1m
  · -- the case `m = 1`
    left
    addarith [hm]
  · -- the case `1 < m`
    obtain hm_eq | hm_right := eq_or_lt_of_le (Nat.le_of_dvd hp' hmp)
    · right
      apply hm_eq
    · have := H _ hm_left hm_right
      contradiction

example : Prime 5 := by
  apply prime_test
  · numbers
  intro m hm_left hm_right
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 2
    constructor <;> numbers
  · use 1
    constructor <;> numbers
  · use 1
    constructor <;> numbers


example {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h_pyth : a ^ 2 + b ^ 2 = c ^ 2) : 3 ≤ a := by
  obtain ha_right | ha_left := le_or_succ_le a 2
  · obtain hb_right | hb_left := le_or_succ_le b 1
    · have hc_right :=
        calc c ^ 2
          _ = a ^ 2 + b ^ 2 := by rw [h_pyth]
          _ ≤ 2 ^ 2 + 1 ^ 2 := by rel [ha_right, hb_right]
          _ < 3 ^ 2 := by numbers
      cancel 2 at hc_right
      interval_cases a <;> interval_cases b <;> interval_cases c <;> numbers at h_pyth
    · have hbc1 :=
        calc b ^ 2
          _ < a ^ 2 + b ^ 2 := by extra
          _ = c ^ 2 := h_pyth
      cancel 2 at hbc1
      have hbc2 :=
        calc c ^ 2
          _ = a ^ 2 + b ^ 2 := by rw [h_pyth]
          _ ≤ 2 ^ 2 + b ^ 2 := by rel [ha_right]
          _ = b ^ 2 + 2 * 2 := by ring
          _ ≤ b ^ 2 + 2 * b := by rel [hb_left]
          _ < b ^ 2 + 2 * b + 1 := by extra
          _ = (b + 1) ^ 2 := by ring
      cancel 2 at hbc2
      have hbc2 := not_le_of_lt hbc2
      contradiction
  · apply ha_left

/-! # Exercises -/


example {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hn : 0 < n) (h : y ^ n ≤ x ^ n) :
    y ≤ x := by
  obtain h1 | h2 := lt_or_ge x y
  · have : x ^ n < y ^ n := by rel [h1]
    have := not_le_of_lt this
    contradiction
  · apply h2

example (n : ℤ) (hn : n ^ 2 ≡ 4 [ZMOD 5]) : n ≡ 2 [ZMOD 5] ∨ n ≡ 3 [ZMOD 5] := by
  mod_cases h : n % 5
  · have :=
      calc
        0 ≡ 0 ^ 2 [ZMOD 5] := by numbers
        _ ≡ n ^ 2 [ZMOD 5] := by rel [h]
        _ ≡ 4 [ZMOD 5] := hn
    numbers at this
  · have :=
      calc
        1 ≡ 1 ^ 2 [ZMOD 5] := by numbers
        _ ≡ n ^ 2 [ZMOD 5] := by rel [h]
        _ ≡ 4 [ZMOD 5] := hn
    numbers at this
  · left
    apply h
  · right
    apply h
  · have :=
      calc
        4 ≡ 4 + 5 * 3 [ZMOD 5] := by extra
        _ ≡ 3 + 4 ^ 2 [ZMOD 5] := by numbers
        _ ≡ 3 + n ^ 2 [ZMOD 5] := by rel [h]
        _ ≡ 3 + 4 [ZMOD 5] := by rel [hn]
        _ = 2 + 5 * 1 := by numbers
        _ ≡ 2 [ZMOD 5] := by extra
    numbers at this

example : Prime 7 := by
  apply prime_test
  · numbers
  · intro m hm_left hm_right
    apply Nat.not_dvd_of_exists_lt_and_lt
    interval_cases m
    · use 3
      constructor <;> numbers
    · use 2
      constructor <;> numbers
    · use 1
      constructor <;> numbers
    · use 1
      constructor <;> numbers
    · use 1
      constructor <;> numbers

example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
  have h3 :=
    calc
      (x + 2) * (x - 2) = x ^ 2 + 2 * x - 2 * x - 4 := by ring
      _ = 0 := by addarith [h1]
  rw [mul_eq_zero] at h3
  obtain h | h := h3
  · have :=
      calc
        3 = 1 + 2 := by numbers
        _ < x + 2 := by rel [h2]
        _ = 0 := h
    contradiction
  · addarith [h]

namespace Nat

example (p : ℕ) (h : Prime p) : p = 2 ∨ Odd p := by
  obtain ⟨hp, hmp⟩ := h
  obtain hp | hp := eq_or_lt_of_le hp
  · left
    addarith [hp]
  · right
    obtain hp_even | hp_odd := Nat.even_or_odd p
    · obtain h1 | h2 := hmp _ hp_even
      · numbers at h1
      · apply ne_of_lt at hp
        contradiction
    · apply hp_odd

/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.ParityModular
import Library.Basic
import Library.Tactic.ModEq

math2001_init

namespace Int


example : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by
  intro h
  have : 0.5 ^ 2 ≥ 0.5 := h 0.5
  numbers at this


example : ¬ 3 ∣ 13 := by
  intro ⟨k, hk⟩
  obtain h4 | h5 := le_or_succ_le k 4
  · have h :=
      calc
        13 = 3 * k := hk
        _  ≤ 3 * 4 := by rel [h4]
    numbers at h
  · have h :=
      calc
        13 = 3 * k := hk
        _  ≥ 3 * 5 := by rel [h5]
    numbers at h

example {x y : ℝ} (h : x + y = 0) : ¬(x > 0 ∧ y > 0) := by
  intro h
  obtain ⟨hx, hy⟩ := h
  have H :=
  calc 0 = x + y := by rw [h]
    _ > 0 := by extra
  numbers at H


example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  intro ⟨n, hn⟩
  obtain h | h := le_or_succ_le n 1
  · have :=
      calc
        2 = n ^ 2 := by rw [hn]
        _ ≤ 1 ^ 2 := by rel [h]
    numbers at this
  · have :=
      calc
        2 = n ^ 2 := by rw [hn]
        _ ≥ 2 ^ 2 := by rel [h]
    numbers at this

example (n : ℤ) : Even n ↔ ¬ Odd n := by
  constructor
  · intro h1 h2
    rw [even_iff_modEq] at h1
    rw [odd_iff_modEq] at h2
    have h :=
    calc 0 ≡ n [ZMOD 2] := by rel [h1]
      _ ≡ 1 [ZMOD 2] := by rel [h2]
    numbers at h -- contradiction!
  · intro h
    obtain h1 | h2 := even_or_odd n
    · apply h1
    · contradiction


example (n : ℤ) : Odd n ↔ ¬ Even n := by
  constructor
  · intro h1 h2
    rw [odd_iff_modEq] at h1
    rw [even_iff_modEq] at h2
    have h :=
      calc
        1 ≡ n [ZMOD 2] := by rel [h1]
        _ ≡ 0 [ZMOD 2] := by rel [h2]
    numbers at h
  · intro h
    obtain h1 | h2 := even_or_odd n
    · contradiction
    · apply h2

example (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 3]) := by
  intro h
  mod_cases hn : n % 3
  · have h :=
      calc
        0 = 0 ^ 2 := by numbers
        _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
        _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h -- contradiction!
  · have h :=
      calc
        1 = 1 ^ 2 := by numbers
        _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
        _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h
  · have h :=
      calc
        1 ≡ 1 + 3 * 1 [ZMOD 3] := by extra
        _ = 2 ^ 2 := by numbers
        _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
        _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h

example {p : ℕ} (k l : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hkl : p = k * l) :
    ¬(Prime p) := by
  have hk : k ∣ p
  · use l
    apply hkl
  intro ⟨h2, hfact⟩
  have : k = 1 ∨ k = p := hfact k hk
  obtain hk1' | hkp' := this
  · contradiction
  · contradiction


example (a b : ℤ) (h : ∃ q, b * q < a ∧ a < b * (q + 1)) : ¬b ∣ a := by
  intro ⟨k, hk⟩
  obtain ⟨q, hq₁, hq₂⟩ := h
  have hb :=
    calc
      0 = a - a := by ring
      _ < b * (q + 1) - b * q := by rel [hq₁, hq₂]
      _ = b := by ring
  have h1 :=
    calc b * k
      _ = a := by rw [hk]
      _ < b * (q + 1) := hq₂
  cancel b at h1
  have h2 :=
    calc b * q
      _ < a := hq₁
      _ = b * k := hk
  cancel b at h2
  apply not_le_of_lt at h1
  have h2 : q + 1 ≤ k := by addarith [h2]
  contradiction

example {p : ℕ} (hp : 2 ≤ p) (T : ℕ) (hTp : p < T ^ 2)
    (H : ∀ (m : ℕ), 1 < m → m < T → ¬ (m ∣ p)) :
    Prime p := by
  apply prime_test hp
  intro m hm1 hmp
  obtain hmT | hmT := lt_or_le m T
  · apply H m hm1 hmT
  intro ⟨l, hl⟩
  have : l ∣ p
  · use m
    rw [hl]
    ring
  have hl1 :=
    calc m * 1
      _ = m := by ring
      _ < p := hmp
      _ = m * l := hl
  cancel m at hl1
  have hl2 :=
    calc T * l
      _ ≤ m * l := by rel [hmT]
      _ = p := by rw [hl]
      _ < T ^ 2 := hTp
      _ = T * T := by ring
  cancel T at hl2
  have : ¬ l ∣ p := H l hl1 hl2
  contradiction


example : Prime 79 := by
  apply better_prime_test (T := 9)
  · numbers
  · numbers
  intro m hm1 hm2
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 39
    constructor <;> numbers
  · use 26
    constructor <;> numbers
  · use 19
    constructor <;> numbers
  · use 15
    constructor <;> numbers
  · use 13
    constructor <;> numbers
  · use 11
    constructor <;> numbers
  · use 9
    constructor <;> numbers

/-! # Exercises -/


example : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  intro ⟨t, ht1, ht2⟩
  have :=
    calc
      5 ≤ t := ht2
      _ ≤ 4 := ht1
  numbers at this

example : ¬ (∃ a : ℝ, a ^ 2 ≤ 8 ∧ a ^ 3 ≥ 30) := by
  intro ⟨a, ha1, ha2⟩
  obtain h1 | h2 := lt_or_le a 0
  · have : a ^ 2 > 0 := sq_pos_of_neg h1
    have :=
      calc 30
        _ ≤ a ^ 3 := ha2
        _ = a ^ 2 * a := by ring
        _ < a ^ 2 * 0 := by rel [h1]
        _ = 0 := by ring
        _ < 30 := by numbers
    numbers at this
  · have ha1 :=
      calc a ^ 2
        _ ≤ 8 := ha1
        _ < 3 ^ 2 := by numbers
    cancel 2 at ha1
    have :=
      calc 30
        _ ≤ a ^ 3 := by rel [ha2]
        _ < 3 ^ 3 := by rel [ha1]
        _ < 30 := by numbers
    numbers at this

example : ¬ Even 7 := by
  apply (odd_iff_not_even 7).1
  use 3
  numbers

example {n : ℤ} (hn : n + 3 = 7) : ¬ (Even n ∧ n ^ 2 = 10) := by
  intro ⟨_, h2⟩
  have :=
    calc 10
    _ = n ^ 2 := by rw [h2]
    _ = (n + 3 - 3) ^ 2 := by ring
    _ = (7 - 3) ^ 2 := by rw [hn]
  numbers at this

example {x : ℝ} (hx : x ^ 2 < 9) : ¬ (x ≤ -3 ∨ x ≥ 3) := by
  have hx :=
    calc x ^ 2
      _ < 9 := hx
      _ = 3 ^ 2 := by numbers
  obtain ⟨h1, h2⟩ := by apply abs_lt_of_sq_lt_sq' hx (by numbers)
  intro h
  obtain h | h := h
  · apply not_le_of_lt h1 h
  · apply not_le_of_lt h2 h

example : ¬ (∃ N : ℕ, ∀ k > N, Nat.Even k) := by
  intro ⟨N, hN⟩
  have h_gt :=
    calc 2 * N + 1
      _ > 2 * N := by extra
      _ = N + N := by ring
      _ ≥ N := by extra
  have h_odd : Nat.Odd (2 * N + 1) := by
    use N
    ring
  have h_even := hN (2 * N + 1) h_gt
  apply (Nat.even_iff_not_odd _).1 at h_even
  contradiction

example (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 4]) := by
  intro h
  mod_cases hn : n % 4
  · have :=
      calc
        0 ≡ 0 ^ 2 [ZMOD 4] := by numbers
        _ ≡ n ^ 2 [ZMOD 4] := by rel [hn]
        _ ≡ 2 [ZMOD 4] := h
    numbers at this
  · have :=
      calc
        1 ≡ 1 ^ 2 [ZMOD 4] := by numbers
        _ ≡ n ^ 2 [ZMOD 4] := by rel [hn]
        _ ≡ 2 [ZMOD 4] := h
    numbers at this
  · have :=
      calc
        0 ≡ 0 + 4 * 1 [ZMOD 4] := by extra
        _ = 2 ^ 2 := by numbers
        _ ≡ n ^ 2 [ZMOD 4] := by rel [hn]
        _ ≡ 2 [ZMOD 4] := h
    numbers at this
  · have :=
      calc
        1 ≡ 1 + 4 * 2 [ZMOD 4] := by extra
        _ = 3 ^ 2 := by numbers
        _ ≡ n ^ 2 [ZMOD 4] := by rel [hn]
        _ ≡ 2 [ZMOD 4] := h
    numbers at this

example : ¬ Prime 1 := by
  intro ⟨h, _⟩
  numbers at h

example : Prime 97 := by
  apply better_prime_test (T := 10) (by numbers) (by numbers)
  intro m hm1 hm2
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 48
    constructor <;> numbers
  · use 32
    constructor <;> numbers
  · use 24
    constructor <;> numbers
  · use 19
    constructor <;> numbers
  · use 16
    constructor <;> numbers
  · use 13
    constructor <;> numbers
  · use 12
    constructor <;> numbers
  · use 10
    constructor <;> numbers

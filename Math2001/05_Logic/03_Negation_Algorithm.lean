/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Rel

math2001_init
set_option pp.funBinderTypes true


example (P Q : Prop) : ¬ (P ∧ Q) ↔ (¬ P ∨ ¬ Q) := by
  constructor
  · intro h
    by_cases hP : P
    · right
      intro hQ
      have hPQ : P ∧ Q
      · constructor
        · apply hP
        · apply hQ
      contradiction
    · left
      apply hP
  · intro h_or ⟨hP, hQ⟩
    obtain hnP | hnQ := h_or <;> contradiction

example :
    ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m) ↔ ∃ m : ℤ, m ≠ 2 ∧ ∀ n : ℤ, n ^ 2 ≠ m :=
  calc ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
      ↔ ∃ m : ℤ, ¬(m ≠ 2 → ∃ n : ℤ, n ^ 2 = m) := by rel [not_forall]
    _ ↔ ∃ m : ℤ, m ≠ 2 ∧ ¬(∃ n : ℤ, n ^ 2 = m) := by rel [not_imp]
    _ ↔ ∃ m : ℤ, m ≠ 2 ∧ ∀ n : ℤ, n ^ 2 ≠ m := by rel [not_exists]


example : ¬(∀ n : ℤ, ∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2)
    ↔ ∃ n : ℤ, ∀ m : ℤ, n ^ 2 ≥ m ∨ m ≥ (n + 1) ^ 2 :=
  calc ¬(∀ n : ℤ, ∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2)
    _ ↔ ∃ n : ℤ, ¬(∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2) := by rel [not_forall]
    _ ↔ ∃ n : ℤ, ∀ m : ℤ, ¬(n ^ 2 < m ∧ m < (n + 1) ^ 2) := by rel [not_exists]
    _ ↔ ∃ n : ℤ, ∀ m : ℤ, ¬n ^ 2 < m ∨ ¬m < (n + 1) ^ 2 := by rel [not_and_or]
    _ ↔ ∃ n : ℤ, ∀ m : ℤ, n ^ 2 ≥ m ∨ m ≥ (n + 1) ^ 2 := by rel [not_lt]

#push_neg ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
  -- ∃ m : ℤ, m ≠ 2 ∧ ∀ (n : ℤ), n ^ 2 ≠ m

#push_neg ¬(∀ n : ℤ, ∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2)
  -- ∃ n : ℤ, ∀ m : ℤ, m ≤ n ^ 2 ∨ (n + 1) ^ 2 ≤ m


#push_neg ¬(∃ m n : ℤ, ∀ t : ℝ, m < t ∧ t < n)
  -- ∀ m n : ℤ, ∃ t : ℝ, t ≤ m ∨ n ≤ t
#push_neg ¬(∀ a : ℕ, ∃ x y : ℕ, x * y ∣ a → x ∣ a ∧ y ∣ a)
  -- ∃ a : ℕ, ∀ x y : ℕ, x * y ∣ a ∧ (¬x ∣ a ∨ ¬y ∣ a)
#push_neg ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
  -- ∃ m : ℤ, m ≠ 2 ∧ ∀ n : ℤ, n ^ 2 ≠ m


example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  push_neg
  intro n
  obtain hn | hn := le_or_succ_le n 1
  · apply ne_of_lt
    calc n ^ 2
      _ ≤ 1 ^ 2 := by rel [hn]
      _ < 2 := by numbers
  · apply ne_of_gt
    calc n ^ 2
      _ ≥ 2 ^ 2 := by rel [hn]
      _ > 2 := by numbers

/-! # Exercises -/


example (P : Prop) : ¬ (¬ P) ↔ P := by
  constructor
  · intro h
    by_cases hP : P
    · apply hP
    · contradiction
  · intro hP hnP
    contradiction

example (P Q : Prop) : ¬ (P → Q) ↔ (P ∧ ¬ Q) := by
  constructor
  · intro hnPimpQ
    by_cases hQ : Q
    · have hPQ : P → Q
      · intro hP
        apply hQ
      contradiction
    · by_cases hP : P
      · constructor
        · apply hP
        · apply hQ
      · have hPQ : P → Q
        · intro hP'
          contradiction
        contradiction
  · intro ⟨hP, hnQ⟩ hPimpQ
    have := hPimpQ hP
    contradiction

example (P : α → Prop) : ¬ (∀ x, P x) ↔ ∃ x, ¬ P x := by
  constructor
  · intro h
    by_cases hx : ∃ x, ¬P x
    · apply hx
    · have : ∀ x, P x
      · intro x
        by_cases hPx : P x
        · apply hPx
        · have : ∃ x, ¬P x
          · use x
            apply hPx
          contradiction
      contradiction
  · intro ⟨x, hnPx⟩ h2
    have := h2 x
    contradiction

example : (¬ ∀ a b : ℤ, a * b = 1 → a = 1 ∨ b = 1)
    ↔ ∃ a b : ℤ, a * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 :=
  calc ¬ ∀ a b : ℤ, a * b = 1 → a = 1 ∨ b = 1
    _ ↔ ∃ a : ℤ, ¬ ∀ b : ℤ, a * b = 1 → a = 1 ∨ b = 1 := by rel [not_forall]
    _ ↔ ∃ a b : ℤ, ¬(a * b = 1 → a = 1 ∨ b = 1) := by rel [not_forall]
    _ ↔ ∃ a b : ℤ, a * b = 1 ∧ ¬(a = 1 ∨ b = 1) := by rel [not_imp]
    _ ↔ ∃ a b : ℤ, a * b = 1 ∧ ¬a = 1 ∧ ¬b = 1 := by rel [not_or]
    _ ↔ ∃ a b : ℤ, a * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 := by rel [ne_eq]

example : (¬ ∃ x : ℝ, ∀ y : ℝ, y ≤ x) ↔ (∀ x : ℝ, ∃ y : ℝ, y > x) :=
  calc ¬ ∃ x : ℝ, ∀ y : ℝ, y ≤ x
    _ ↔ ∀ x : ℝ, ¬ ∀ y : ℝ, y ≤ x := by rel [not_exists]
    _ ↔ ∀ x : ℝ, ∃ y : ℝ, ¬(y ≤ x) := by rel [not_forall]
    _ ↔ ∀ x : ℝ, ∃ y : ℝ, y > x := by rel [not_le]

example : ¬ (∃ m : ℤ, ∀ n : ℤ, m = n + 5) ↔ ∀ m : ℤ, ∃ n : ℤ, m ≠ n + 5 :=
  calc ¬ (∃ m : ℤ, ∀ n : ℤ, m = n + 5)
    _ ↔ ∀ m : ℤ, ¬ ∀ n : ℤ, m = n + 5 := by rel [not_exists]
    _ ↔ ∀ m : ℤ, ∃ n : ℤ, ¬m = n + 5 := by rel [not_forall]
    _ ↔ ∀ m : ℤ, ∃ n : ℤ, m ≠ n + 5 := by rel [ne_eq]

#push_neg ¬(∀ n : ℕ, n > 0 → ∃ k l : ℕ, k < n ∧ l < n ∧ k ≠ l)
  -- ∃ n : ℕ, n > 0, ∀ k l : ℕ, n ≤ k ∨ n ≤ l ∨ k = l
#push_neg ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
  -- ∃ m : ℤ, m ≠ 2 ∧ ∀ n : ℤ, n ^ 2 ≠ m
#push_neg ¬(∃ x : ℝ, ∀ y : ℝ, ∃ m : ℤ, x < y * m ∧ y * m < m)
  -- ∀ x : ℝ, ∃ y : ℝ, ∀ m : ℤ, y * m ≤ x ∨ m ≤ y * m
#push_neg ¬(∃ x : ℝ, ∀ q : ℝ, q > x → ∃ m : ℕ, q ^ m > x)
  -- ∀ x : ℝ, ∃ q : ℝ, q > x, ∀ m : ℕ, q ^ m ≤ x


example : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by
  push_neg
  use 0.5
  numbers

example : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  push_neg
  intro t
  by_cases ht : 4 < t
  · left
    apply ht
  · right
    apply le_of_not_lt at ht
    calc
      t ≤ 4 := ht
      _ < 5 := by numbers

example : ¬ Int.Even 7 := by
  dsimp [Int.Even]
  push_neg
  intro k hk
  have hk1 :=
    calc 2 * k
      _ = 7 := by rw [hk]
      _ < 2 * 4 := by numbers
  have hk2 :=
    calc 2 * k
      _ = 7 := by rw [hk]
      _ > 2 * 3 := by numbers
  cancel 2 at hk1
  cancel 2 at hk2
  interval_cases k

example {p : ℕ} (k : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hk : k ∣ p) : ¬ Prime p := by
  dsimp [Prime]
  push_neg
  by_cases hp : p < 2
  · left
    apply hp
  · right
    use k
    constructor
    · apply hk
    constructor
    · apply hk1
    · apply hkp

example : ¬ ∃ a : ℤ, ∀ n : ℤ, 2 * a ^ 3 ≥ n * a + 7 := by
  push_neg
  intro a
  use 2 * a ^ 2
  calc 2 * a ^ 3
    _ < 2 * a ^ 3 + 7 := by extra
    _ = 2 * a ^ 2 * a + 7 := by ring

example {p : ℕ} (hp : ¬ Prime p) (hp2 : 2 ≤ p) : ∃ m, 2 ≤ m ∧ m < p ∧ m ∣ p := by
  have H : ¬ (∀ (m : ℕ), 2 ≤ m → m < p → ¬m ∣ p)
  · intro H
    have : Prime p
    · apply prime_test
      · apply hp2
      · intro m hm1 hm2 hmp
        have := H m hm1 hm2
        contradiction
    contradiction
  push_neg at H
  apply H

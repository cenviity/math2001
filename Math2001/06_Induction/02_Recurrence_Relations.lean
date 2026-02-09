/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Tactic.GCongr
import Library.Basic
import Library.Tactic.ModEq

math2001_init

namespace Int


def a (n : ℕ) : ℕ := 2 ^ n


#eval a 20 -- infoview displays `1048576`


def b : ℕ → ℤ
  | 0 => 3
  | n + 1 => b n ^ 2 - 2


#eval b 7 -- infoview displays `316837008400094222150776738483768236006420971486980607`


example (n : ℕ) : Odd (b n) := by
  simple_induction n with k hk
  · -- base case
    use 1
    calc b 0 = 3 := by rw [b]
      _ = 2 * 1 + 1 := by numbers
  · -- inductive step
    obtain ⟨x, hx⟩ := hk
    use 2 * x ^ 2 + 2 * x - 1
    calc b (k + 1) = b k ^ 2 - 2 := by rw [b]
      _ = (2 * x + 1) ^ 2 - 2 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + 2 * x - 1) + 1 := by ring


example (n : ℕ) : b n ≡ 1 [ZMOD 2] := by
  simple_induction n with k hk
  · rw [b]
    use 1
    numbers
  · calc b (k + 1)
      _ = b k ^ 2 - 2 := by rw [b]
      _ ≡ 1 ^ 2 - 2 [ZMOD 2] := by rel [hk]
      _ = 2 * -1 + 1 := by numbers
      _ ≡ 1 [ZMOD 2] := by extra


def x : ℕ → ℤ
  | 0 => 5
  | n + 1 => 2 * x n - 1


#eval x 0
#eval x 1
#eval x 2
#eval x 3
#eval x 4
#eval x 5


example (n : ℕ) : x n ≡ 1 [ZMOD 4] := by
  simple_induction n with k IH
  · -- base case
    rw [x]
    use 1
    numbers
  · -- inductive step
    calc x (k + 1)
      _ = 2 * x k - 1 := by rw [x]
      _ ≡ 2 * 1 - 1 [ZMOD 4] := by rel [IH]
      _ ≡ 1 [ZMOD 4] := by numbers

example (n : ℕ) : x n = 2 ^ (n + 2) + 1 := by
  simple_induction n with k IH
  · -- base case
    calc x 0 = 5 := by rw [x]
      _ = 2 ^ (0 + 2) + 1 := by numbers
  · -- inductive step
    calc x (k + 1) = 2 * x k - 1 := by rw [x]
      _ = 2 * (2 ^ (k + 2) + 1) - 1 := by rw [IH]
      _ = 2 ^ ((k + 1) + 2) + 1 := by ring


def A : ℕ → ℚ
  | 0 => 0
  | n + 1 => A n + (n + 1)


example (n : ℕ) : A n = n * (n + 1) / 2 := by
  simple_induction n with k IH
  · -- base case
    calc A 0 = 0 := by rw [A]
      _ = 0 * (0 + 1) / 2 := by numbers
  · -- inductive step
    calc
      A (k + 1) = A k + (k + 1) := by rw [A]
      _ = k * (k + 1) / 2 + (k + 1) := by rw [IH]
      _ = (k + 1) * (k + 1 + 1) / 2 := by ring



def factorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

notation:10000 n "!" => factorial n


example (n : ℕ) : ∀ d, 1 ≤ d → d ≤ n → d ∣ n ! := by
  simple_induction n with k IH
  · -- base case
    intro k hk1 hk
    interval_cases k
  · -- inductive step
    intro d hk1 hk
    obtain hk | hk : d = k + 1 ∨ d < k + 1 := eq_or_lt_of_le hk
    · -- case 1: `d = k + 1`
      use (k !)
      calc ((k + 1)!)
        _ = (k + 1) * k ! := by rw [factorial]
        _ = d * k ! := by rw [hk]
    · -- case 2: `d < k + 1`
      have hk := Nat.le_of_lt_succ hk
      obtain ⟨x, hx⟩ : d ∣ k ! := IH d hk1 hk
      use (k + 1) * x
      calc ((k + 1) !)
        _ = (k + 1) * k ! := by rw [factorial]
        _ = (k + 1) * (d * x) := by rw [hx]
        _ = d * ((k + 1) * x) := by ring

example (n : ℕ) : (n + 1)! ≥ 2 ^ n := by
  simple_induction n with k IH
  · calc ((0 + 1)!)
      _ = (0 + 1) * 0! := by dsimp [factorial]
      _ = (0 + 1) * 1 := by rw [factorial]
      _ ≥ 2 ^ 0 := by numbers
  · calc ((k + 1 + 1)!)
      _ = (k + 1 + 1) * (k + 1)! := by rw [factorial]
      _ ≥ (k + 1 + 1) * 2 ^ k := by rel [IH]
      _ = k * 2 ^ k + 2 ^ (k + 1) := by ring
      _ ≥ 2 ^ (k + 1) := by extra


/-! # Exercises -/


def c : ℕ → ℤ
  | 0 => 7
  | n + 1 => 3 * c n - 10

example (n : ℕ) : Odd (c n) := by
  simple_induction n with k IH
  · rw [c]
    use 3
    numbers
  · obtain ⟨x, hx⟩ := IH
    use 3 * x - 4
    calc c (k + 1)
      _ = 3 * c k - 10 := by rw [c]
      _ = 3 * (2 * x + 1) - 10 := by rw [hx]
      _ = 2 * (3 * x - 4) + 1 := by ring

example (n : ℕ) : c n ≡ 1 [ZMOD 2] := by
  simple_induction n with k IH
  · rw [c]
    use 3
    numbers
  · calc c (k + 1)
      _ = 3 * c k - 10 := by rw [c]
      _ ≡ 3 * 1 - 10 [ZMOD 2] := by rel [IH]
      _ = 2 * -4 + 1 := by ring
      _ ≡ 1 [ZMOD 2] := by extra

example (n : ℕ) : c n = 2 * 3 ^ n + 5 := by
  simple_induction n with k IH
  · rw [c]
    numbers
  · calc c (k + 1)
      _ = 3 * c k - 10 := by rw [c]
      _ = 3 * (2 * 3 ^ k + 5) - 10 := by rw [IH]
      _ = 2 * 3 ^ (k + 1) + 5 := by ring

def y : ℕ → ℕ
  | 0 => 2
  | n + 1 => (y n) ^ 2

example (n : ℕ) : y n = 2 ^ (2 ^ n) := by
  simple_induction n with k IH
  · rw [y]
    numbers
  · calc y (k + 1)
      _ = (y k) ^ 2 := by rw [y]
      _ = (2 ^ 2 ^ k) ^ 2 := by rw [IH]
      _ = 2 ^ 2 ^ (k + 1) := by ring

def B : ℕ → ℚ
  | 0 => 0
  | n + 1 => B n + (n + 1 : ℚ) ^ 2

example (n : ℕ) : B n = n * (n + 1) * (2 * n + 1) / 6 := by
  simple_induction n with k IH
  · rw [B]
    numbers
  · calc B (k + 1)
      _ = B k + (k + 1) ^ 2 := by rw [B]
      _ = k * (k + 1) * (2 * k + 1) / 6 + (k + 1) ^ 2 := by rw [IH]
      _ = (k + 1) * (k + 1 + 1) * (2 * (k + 1) + 1) / 6 := by ring

def S : ℕ → ℚ
  | 0 => 1
  | n + 1 => S n + 1 / 2 ^ (n + 1)

example (n : ℕ) : S n = 2 - 1 / 2 ^ n := by
  simple_induction n with k IH
  · rw [S]
    numbers
  · calc S (k + 1)
      _ = S k + 1 / 2 ^ (k + 1) := by rw [S]
      _ = 2 - 1 / 2 ^ k + 1 / 2 ^ (k + 1) := by rw [IH]
      _ = 2 - 1 / 2 ^ (k + 1) := by ring

example (n : ℕ) : 0 < n ! := by
  simple_induction n with k IH
  · rw [factorial]
    numbers
  · calc ((k + 1) !)
      _ = (k + 1) * k ! := by rw [factorial]
      _ > (k + 1) * 0 := by rel [IH]
      _ = 0 := by ring

example {n : ℕ} (hn : 2 ≤ n) : Nat.Even (n !) := by
  induction_from_starting_point n, hn with k hk IH
  · use 1
    dsimp [factorial]
  · obtain ⟨x, hx⟩ := IH
    use (k + 1) * x
    calc ((k + 1) !)
      _ = (k + 1) * k ! := by rw [factorial]
      _ = (k + 1) * (2 * x) := by rw [hx]
      _ = 2 * ((k + 1) * x) := by ring

example (n : ℕ) : (n + 1) ! ≤ (n + 1) ^ n := by
  simple_induction n with k IH
  · dsimp [factorial]
    numbers
  · have hpow : (k + 1) ^ k ≤ (k + 1 + 1) ^ k
    · apply Nat.pow_le_pow_of_le_left (by extra)
    calc ((k + 1 + 1) !)
      _ = (k + 1 + 1) * (k + 1) ! := by rw [factorial]
      _ ≤ (k + 1 + 1) * (k + 1) ^ k := by rel [IH]
      _ ≤ (k + 1 + 1) * (k + 1 + 1) ^ k := by rel [hpow]
      _ = (k + 1 + 1) ^ (k + 1) := by ring

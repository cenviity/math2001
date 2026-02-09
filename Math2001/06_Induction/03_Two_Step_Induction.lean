/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Tactic.GCongr
import Library.Basic
import Library.Tactic.ModEq

math2001_init

open Int


def a : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | n + 2 => a (n + 1) + 2 * a n


#eval a 5 -- infoview displays `31`


example (n : ℕ) : a n = 2 ^ n + (-1) ^ n := by
  two_step_induction n with k IH1 IH2
  . calc a 0 = 2 := by rw [a]
      _ = 2 ^ 0 + (-1) ^ 0 := by numbers
  . calc a 1 = 1 := by rw [a]
      _ = 2 ^ 1 + (-1) ^ 1 := by numbers
  calc
    a (k + 2)
      = a (k + 1) + 2 * a k := by rw [a]
    _ = (2 ^ (k + 1) + (-1) ^ (k + 1)) + 2 * (2 ^ k + (-1) ^ k) := by rw [IH1, IH2]
    _ = 2 ^ (k + 2) + (-1) ^ (k + 2) := by ring


example {m : ℕ} (hm : 1 ≤ m) : a m ≡ 1 [ZMOD 6] ∨ a m ≡ 5 [ZMOD 6] := by
  have H : ∀ n : ℕ, 1 ≤ n →
      (a n ≡ 1 [ZMOD 6] ∧ a (n + 1) ≡ 5 [ZMOD 6])
    ∨ (a n ≡ 5 [ZMOD 6] ∧ a (n + 1) ≡ 1 [ZMOD 6])
  · intro n hn
    induction_from_starting_point n, hn with k hk IH
    · left
      constructor
      calc a 1 = 1 := by rw [a]
        _ ≡ 1 [ZMOD 6] := by extra
      calc a (1 + 1) = 1 + 2 * 2 := by rw [a, a, a]
        _ = 5 := by numbers
        _ ≡ 5 [ZMOD 6] := by extra
    · obtain ⟨IH1, IH2⟩ | ⟨IH1, IH2⟩ := IH
      · right
        constructor
        · apply IH2
        calc a (k + 1 + 1) = a (k + 1) + 2 * a k := by rw [a]
          _ ≡ 5 + 2 * 1 [ZMOD 6] := by rel [IH1, IH2]
          _ = 6 * 1 + 1 := by numbers
          _ ≡ 1 [ZMOD 6] := by extra
      · left
        constructor
        · apply IH2
        calc a (k + 1 + 1) = a (k + 1) + 2 * a k := by rw [a]
          _ ≡ 1 + 2 * 5 [ZMOD 6] := by rel [IH1, IH2]
          _ = 6 * 1 + 5 := by numbers
          _ ≡ 5 [ZMOD 6] := by extra
  obtain ⟨H1, H2⟩ | ⟨H1, H2⟩ := H m hm
  · left
    apply H1
  · right
    apply H1


def F : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => F (n + 1) + F n


#eval (List.range 11).map F


example (n : ℕ) : F n ≤ 2 ^ n := by
  two_step_induction n with k IH1 IH2
  · calc F 0 = 1 := by rw [F]
      _ ≤ 2 ^ 0 := by numbers
  · calc F 1 = 1 := by rw [F]
      _ ≤ 2 ^ 1 := by numbers
  · calc F (k + 2) = F (k + 1) + F k := by rw [F]
      _ ≤ 2 ^ (k + 1) + 2 ^ k := by rel [IH1, IH2]
      _ ≤ 2 ^ (k + 1) + 2 ^ k + 2 ^ k := by extra
      _ = 2 ^ (k + 2) := by ring


example (n : ℕ) : F (n + 1) ^ 2 - F (n + 1) * F n - F n ^ 2 = - (-1) ^ n := by
  simple_induction n with k IH
  · calc F 1 ^ 2 - F 1 * F 0 - F 0 ^ 2 = 1 ^ 2 - 1 * 1 - 1 ^ 2 := by rw [F, F]
      _ = - (-1) ^ 0 := by numbers
  · calc F (k + 2) ^ 2 - F (k + 2) * F (k + 1) - F (k + 1) ^ 2
        = (F (k + 1) + F k) ^ 2 - (F (k + 1) + F k) * F (k + 1)
            - F (k + 1) ^ 2 := by rw [F]
      _ = - (F (k + 1) ^ 2 - F (k + 1) * F k - F k ^ 2) := by ring
      _ = - -(-1) ^ k := by rw [IH]
      _ = -(-1) ^ (k + 1) := by ring


def d : ℕ → ℤ
  | 0 => 3
  | 1 => 1
  | k + 2 => 3 * d (k + 1) + 5 * d k


#eval d 2 -- infoview displays `18`
#eval d 3 -- infoview displays `59`
#eval d 4 -- infoview displays `267`
#eval d 5 -- infoview displays `1096`
#eval d 6 -- infoview displays `4623`
#eval d 7 -- infoview displays `19349`


#eval 4 ^ 2 -- infoview displays `16`
#eval 4 ^ 3 -- infoview displays `64`
#eval 4 ^ 4 -- infoview displays `256`
#eval 4 ^ 5 -- infoview displays `1024`
#eval 4 ^ 6 -- infoview displays `4096`
#eval 4 ^ 7 -- infoview displays `16384`


example : forall_sufficiently_large n : ℕ, d n ≥ 4 ^ n := by
  dsimp
  use 4
  intro n hn
  two_step_induction_from_starting_point n, hn with k hk IH1 IH2
  · calc d 4 = 267 := by rfl
      _ ≥ 4 ^ 4 := by numbers
  · calc d 5 = 1096 := by rfl
      _ ≥ 4 ^ 5 := by numbers
  calc d (k + 2) = 3 * d (k + 1) + 5 * d k := by rw [d]
    _ ≥ 3 * 4 ^ (k + 1) + 5 * 4 ^ k := by rel [IH1, IH2]
    _ = 16 * 4 ^ k + 4 ^ k := by ring
    _ ≥ 16 * 4 ^ k := by extra
    _ = 4 ^ (k + 2) := by ring

/-! # Exercises -/


def b : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => 5 * b (n + 1) - 6 * b n

example (n : ℕ) : b n = 3 ^ n - 2 ^ n := by
  two_step_induction n with k IH1 IH2
  · rw [b]
    numbers
  · rw [b]
    numbers
  · calc b (k + 1 + 1)
      _ = 5 * b (k + 1) - 6 * b k := by rw [b]
      _ = 5 * (3 ^ (k + 1) - 2 ^ (k + 1)) - 6 * (3 ^ k - 2 ^ k) := by rw [IH1, IH2]
      _ = 3 ^ (k + 1 + 1) - 2 ^ (k + 1 + 1) := by ring

def c : ℕ → ℤ
  | 0 => 3
  | 1 => 2
  | n + 2 => 4 * c n

example (n : ℕ) : c n = 2 * 2 ^ n + (-2) ^ n := by
  two_step_induction n with k IH1 IH2
  · rw [c]
    numbers
  · rw [c]
    numbers
  · calc c (k + 1 + 1)
      _ = 4 * c k := by rw [c]
      _ = 4 * (2 * 2 ^ k + (-2) ^ k) := by rw [IH1]
      _ = 2 * 2 ^ (k + 1 + 1) + (-2) ^ (k + 1 + 1) := by ring

def t : ℕ → ℤ
  | 0 => 5
  | 1 => 7
  | n + 2 => 2 * t (n + 1) - t n

example (n : ℕ) : t n = 2 * n + 5 := by
  two_step_induction n with k IH1 IH2
  · rw [t]
    numbers
  · rw [t]
    numbers
  · calc t (k + 1 + 1)
      _ = 2 * t (k + 1) - t k := by rw [t]
      _ = 2 * (2 * (k + 1) + 5) - (2 * k + 5) := by rw [IH1, IH2]
      _ = 2 * (k + 1 + 1) + 5 := by ring

def q : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | n + 2 => 2 * q (n + 1) - q n + 6 * n + 6

example (n : ℕ) : q n = (n:ℤ) ^ 3 + 1 := by
  two_step_induction n with k IH1 IH2
  · rw [q]
    numbers
  · rw [q]
    numbers
  · calc q (k + 1 + 1)
      _ = 2 * q (k + 1) - q k + 6 * k + 6 := by rw [q]
      _ = 2 * ((k + 1) ^ 3 + 1) - (k ^ 3 + 1) + 6 * k + 6 := by rw [IH1, IH2]
      _ = (k + 1 + 1) ^ 3 + 1 := by ring

def s : ℕ → ℤ
  | 0 => 2
  | 1 => 3
  | n + 2 => 2 * s (n + 1) + 3 * s n

#eval (List.range 11).map (s · % 5)

example (m : ℕ) : s m ≡ 2 [ZMOD 5] ∨ s m ≡ 3 [ZMOD 5] := by
  have H : ∀ m : ℕ,
      (s m ≡ 2 [ZMOD 5] ∧ s (m + 1) ≡ 3 [ZMOD 5])
    ∨ (s m ≡ 3 [ZMOD 5] ∧ s (m + 1) ≡ 2 [ZMOD 5])
  · intro m
    two_step_induction m with k IH1 IH2
    · left
      constructor <;> rw [s] <;> numbers
    · right
      constructor <;> rw [s]
      · numbers
      · calc (2 : ℤ) * 3 + 3 * 2
          _ = 2 * 5 + 2 := by numbers
          _ ≡ 2 [ZMOD 5] := by extra
    · obtain ⟨hk, hk_succ⟩ | ⟨hk, hk_succ⟩ := IH1
      · left
        obtain ⟨hk_succ', -⟩ | ⟨-, hk_succ_succ⟩ := IH2
        · have :=
            calc
              3 ≡ s (k + 1) [ZMOD 5] := by rel [hk_succ]
              _ ≡ 2 [ZMOD 5] := hk_succ'
          numbers at this
        · constructor
          · apply hk_succ_succ
          · calc s (k + 3)
              _ = 2 * s (k + 2) + 3 * s (k + 1) := by rw [s]
              _ ≡ 2 * 2 + 3 * 3 [ZMOD 5] := by rel [hk_succ, hk_succ_succ]
              _ = 5 * 2 + 3 := by numbers
              _ ≡ 3 [ZMOD 5] := by extra
      · right
        obtain ⟨-, hk_succ_succ⟩ | ⟨hk_succ', -⟩ := IH2
        · constructor
          · apply hk_succ_succ
          · calc s (k + 3)
              _ = 2 * s (k + 2) + 3 * s (k + 1) := by rw [s]
              _ ≡ 2 * 3 + 3 * 2 [ZMOD 5] := by rel [hk_succ, hk_succ_succ]
              _ = 5 * 2 + 2 := by numbers
              _ ≡ 2 [ZMOD 5] := by extra
        · have :=
            calc
              2 ≡ s (k + 1) [ZMOD 5] := by rel [hk_succ]
              _ ≡ 3 [ZMOD 5] := hk_succ'
          numbers at this
  obtain ⟨H1, -⟩ | ⟨H1, -⟩ := H m
  · left
    apply H1
  · right
    apply H1

def p : ℕ → ℤ
  | 0 => 2
  | 1 => 3
  | n + 2 => 6 * p (n + 1) - p n

#eval (List.range 11).map (p · % 7)

example (m : ℕ) : p m ≡ 2 [ZMOD 7] ∨ p m ≡ 3 [ZMOD 7] := by
  have H : ∀ n : ℕ,
      (p n ≡ 3 [ZMOD 7] ∧ p (n + 1) ≡ 2 [ZMOD 7])
    ∨ (p n ≡ 2 [ZMOD 7] ∧ p (n + 1) ≡ 2 [ZMOD 7])
    ∨ (p n ≡ 2 [ZMOD 7] ∧ p (n + 1) ≡ 3 [ZMOD 7])
  · intro n
    two_step_induction n with k IH1 IH2
    · right
      right
      dsimp [p]
      constructor <;> numbers
    · left
      dsimp [p]
      constructor
      · numbers
      · calc (6 : ℤ) * 3 - 2
          _ = 7 * 2 + 2 := by numbers
          _ ≡ 2 [ZMOD 7] := by extra
    · obtain ⟨hk, hk_succ⟩ | ⟨hk, hk_succ⟩ | ⟨hk, hk_succ⟩ := IH1
      · right
        right
        obtain ⟨hk_succ', -⟩ | ⟨hk_succ, hk_succ_succ⟩ | ⟨hk_succ, hk_succ_succ⟩ := IH2
        · have :=
            calc
              2 ≡ p (k + 1) [ZMOD 7] := by rel [hk_succ]
              _ ≡ 3 [ZMOD 7] := hk_succ'
          numbers at this
        · have hk_succ_succ_succ :=
            calc p (k + 3)
              _ = 6 * p (k + 2) - p (k + 1) := by rw [p]
              _ ≡ 6 * 2 - 2 [ZMOD 7] := by rel [hk_succ, hk_succ_succ]
              _ = 7 * 1 + 3 := by numbers
              _ ≡ 3 [ZMOD 7] := by extra
          constructor
          · apply hk_succ_succ
          · apply hk_succ_succ_succ
        · have :=
            calc
              3 ≡ p (k + 2) [ZMOD 7] := by rel [hk_succ_succ]
              _ = 6 * p (k + 1) - p k := by rw [p]
              _ ≡ 6 * 2 - 3 [ZMOD 7] := by rel [hk, hk_succ]
              _ = 7 * 1 + 2 := by numbers
              _ ≡ 2 [ZMOD 7] := by extra
          numbers at this
      · left
        obtain ⟨hk_succ', -⟩ | ⟨hk_succ, hk_succ_succ'⟩ | ⟨hk_succ, hk_succ_succ⟩ := IH2
        · have :=
            calc
              2 ≡ p (k + 1) [ZMOD 7] := by rel [hk_succ]
              _ ≡ 3 [ZMOD 7] := hk_succ'
          numbers at this
        · have :=
            calc
              2 ≡ p (k + 2) [ZMOD 7] := by rel [hk_succ_succ']
              _ = 6 * p (k + 1) - p k := by rw [p]
              _ ≡ 6 * 2 - 2 [ZMOD 7] := by rel [hk, hk_succ]
              _ = 7 * 1 + 3 := by numbers
              _ ≡ 3 [ZMOD 7] := by extra
          numbers at this
        · have hk_succ_succ_succ :=
            calc p (k + 3)
              _ = 6 * p (k + 2) - p (k + 1) := by rw [p]
              _ ≡ 6 * 3 - 2 [ZMOD 7] := by rel [hk_succ, hk_succ_succ]
              _ = 7 * 2 + 2 := by numbers
              _ ≡ 2 [ZMOD 7] := by extra
          constructor
          · apply hk_succ_succ
          · apply hk_succ_succ_succ
      · right
        left
        obtain ⟨hk_succ, hk_succ_succ⟩ | ⟨hk_succ', -⟩ | ⟨hk_succ', -⟩ := IH2
        · have hk_succ_succ_succ :=
            calc p (k + 3)
              _ = 6 * p (k + 2) - p (k + 1) := by rw [p]
              _ ≡ 6 * 2 - 3 [ZMOD 7] := by rel [hk_succ, hk_succ_succ]
              _ = 7 * 1 + 2 := by numbers
              _ ≡ 2 [ZMOD 7] := by extra
          constructor
          · apply hk_succ_succ
          · apply hk_succ_succ_succ
        · have :=
            calc
              3 ≡ p (k + 1) [ZMOD 7] := by rel [hk_succ]
              _ ≡ 2 [ZMOD 7] := hk_succ'
          numbers at this
        · have :=
            calc
              3 ≡ p (k + 1) [ZMOD 7] := by rel [hk_succ]
              _ ≡ 2 [ZMOD 7] := by rel [hk_succ']
          numbers at this
  obtain ⟨H1, -⟩ | ⟨H1, -⟩ | ⟨H1, -⟩ := H m
  · right
    apply H1
  · left
    apply H1
  · left
    apply H1

def r : ℕ → ℤ
  | 0 => 2
  | 1 => 0
  | n + 2 => 2 * r (n + 1) + r n

#eval (List.range 11).map (r ·)
#eval (List.range 11).map (2 ^ ·)

example : forall_sufficiently_large n : ℕ, r n ≥ 2 ^ n := by
  use 7
  intro n hn
  two_step_induction_from_starting_point n, hn with k hk IH1 IH2
  · dsimp [r]
    numbers
  · dsimp [r]
    numbers
  · calc r (k + 2)
      _ = 2 * r (k + 1) + r k := by rw [r]
      _ ≥ 2 * 2 ^ (k + 1) + 2 ^ k := by rel [IH1, IH2]
      _ ≥ 2 * 2 ^ (k + 1) := by extra
      _ = 2 ^ (k + 2) := by ring

example : forall_sufficiently_large n : ℕ,
    (0.4:ℚ) * 1.6 ^ n < F n ∧ F n < (0.5:ℚ) * 1.7 ^ n := by
  use 8
  intro x hx
  two_step_induction_from_starting_point x, hx with k hk IH1 IH2
  · norm_cast
  · norm_cast
  · obtain ⟨IH1_1, IH1_2⟩ := IH1
    obtain ⟨IH2_1, IH2_2⟩ := IH2
    constructor
    · have h_sq_le_succ : (1.6 : ℚ) ^ 2 < 1.6 + 1 := by numbers
      calc (0.4 : ℚ) * 1.6 ^ (k + 2)
        _ = 0.4 * 1.6 ^ 2 * 1.6 ^ k := by ring
        _ < 0.4 * (1.6 + 1) * 1.6 ^ k := by rel [h_sq_le_succ]
        _ = 0.4 * 1.6 ^ (k + 1) + 0.4 * 1.6 ^ k := by ring
        _ < F (k + 1) + F k := by rel [IH1_1, IH2_1]
        _ = F (k + 2) := by norm_cast
    · have h_sq_gt_succ : (1.7 : ℚ) ^ 2 > 1.7 + 1 := by numbers
      calc (0.5 : ℚ) * 1.7 ^ (k + 2)
        _ = 0.5 * 1.7 ^ 2 * 1.7 ^ k := by ring
        _ > 0.5 * (1.7 + 1) * 1.7 ^ k := by rel [h_sq_gt_succ]
        _ = 0.5 * 1.7 ^ (k + 1) + 0.5 * 1.7 ^ k := by ring
        _ > F (k + 1) + F k := by rel [IH1_2, IH2_2]
        _ = F (k + 2) := by norm_cast

/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic
import Library.Theory.ModEq.Defs

math2001_init


def fmod (n d : ℤ) : ℤ :=
  if n * d < 0 then
    fmod (n + d) d
  else if h2 : 0 < d * (n - d) then
    fmod (n - d) d
  else if h3 : n = d then
    0
  else
    n
termination_by _ n d => 2 * n - d

def fdiv (n d : ℤ) : ℤ :=
  if n * d < 0 then
    fdiv (n + d) d - 1
  else if 0 < d * (n - d) then
    fdiv (n - d) d + 1
  else if h3 : n = d then
    1
  else
    0
termination_by _ n d => 2 * n - d


#eval fmod 11 4 -- infoview displays `3`
#eval fdiv 11 4 -- infoview displays `2`


theorem fmod_add_fdiv (n d : ℤ) : fmod n d + d * fdiv n d = n := by
  rw [fdiv, fmod]
  split_ifs with h1 h2 h3 <;> push_neg at *
  · -- case `n * d < 0`
    have IH := fmod_add_fdiv (n + d) d -- inductive hypothesis
    calc fmod (n + d) d + d * (fdiv (n + d) d - 1)
        = (fmod (n + d) d + d * fdiv (n + d) d) - d := by ring
      _ = (n + d) - d := by rw [IH]
      _ = n := by ring
  · -- case `0 < d * (n - d)`
    have IH := fmod_add_fdiv (n - d) d -- inductive hypothesis
    calc fmod (n - d) d + d * (fdiv (n - d) d + 1)
        = (fmod (n - d) d + d * fdiv (n - d) d) + d := by ring
        _ = n := by addarith [IH]
  · -- case `n = d`
    calc 0 + d * 1 = d := by ring
      _ = n := by rw [h3]
  · -- last case
    ring
termination_by _ n d => 2 * n - d



theorem fmod_nonneg_of_pos (n : ℤ) {d : ℤ} (hd : 0 < d) : 0 ≤ fmod n d := by
  rw [fmod]
  split_ifs with h1 h2 h3 <;> push_neg at *
  · -- case `n * d < 0`
    have IH := fmod_nonneg_of_pos (n + d) hd -- inductive hypothesis
    apply IH
  · -- case `0 < d * (n - d)`
    have IH := fmod_nonneg_of_pos (n - d) hd -- inductive hypothesis
    apply IH
  · -- case `n = d`
    extra
  · -- last case
    cancel d at h1
termination_by _ n d hd => 2 * n - d


theorem fmod_lt_of_pos (n : ℤ) {d : ℤ} (hd : 0 < d) : fmod n d < d := by
  rw [fmod]
  split_ifs with h1 h2 h3 <;> push_neg at *
  · -- case `n * d < 0`
    have IH := fmod_lt_of_pos (n + d) hd -- inductive hypothesis
    apply IH
  · -- case `0 < d * (n - d)`
    have IH := fmod_lt_of_pos (n - d) hd -- inductive hypothesis
    apply IH
  · -- case `n = d`
    apply hd
  · -- last case
    have h4 :=
    calc 0 ≤ - d * (n - d) := by addarith [h2]
      _ = d * (d - n) := by ring
    cancel d at h4
    apply lt_of_le_of_ne
    · addarith [h4]
    · apply h3
termination_by _ n d hd => 2 * n - d


example (a b : ℤ) (h : 0 < b) : ∃ r : ℤ, 0 ≤ r ∧ r < b ∧ a ≡ r [ZMOD b] := by
  use fmod a b
  constructor
  · apply fmod_nonneg_of_pos a h
  constructor
  · apply fmod_lt_of_pos a h
  · use fdiv a b
    have Hab : fmod a b + b * fdiv a b = a := fmod_add_fdiv a b
    addarith [Hab]

/-! # Exercises -/


theorem lt_fmod_of_neg (n : ℤ) {d : ℤ} (hd : d < 0) : d < fmod n d := by
  rw [fmod]
  split_ifs with h1 h2 h3 <;> push_neg at *
  · apply lt_fmod_of_neg (n + d) hd
  · apply lt_fmod_of_neg (n - d) hd
  · apply hd
  · have hd' : 0 < -d := by addarith [hd]
    have h4 :=
      calc
        0 ≤ - d * (n - d) := by addarith [h2]
        _ = -d * (n - d) := by ring
    cancel -d at h4
    apply lt_of_le_of_ne
    · addarith [h4]
    · apply h3.symm
  termination_by _ n d hd => 2 * n - d

def T (n : ℤ) : ℤ :=
  if 0 < n then
    T (1 - n) + 2 * n - 1
  else if 0 < -n then
    T (-n)
  else
    0
termination_by T n => 3 * n - 1

theorem T_eq (n : ℤ) : T n = n ^ 2 := by
  rw [T]
  split_ifs with h1 h2 <;> push_neg at *
  · calc T (1 - n) + 2 * n - 1
      _ = (1 - n) ^ 2 + 2 * n - 1 := by rw [T_eq]
      _ = n ^ 2 := by ring
  · calc T (-n)
      _ = (-n) ^ 2 := by rw [T_eq]
      _ = n ^ 2 :=  by ring
  · have h : n = 0 := le_antisymm h1 (by addarith [h2])
    calc
      0 = 0 ^ 2 := by numbers
      _ = n ^ 2 := by rw [h]
  termination_by _ n => 3 * n - 1

theorem uniqueness (a b : ℤ) (h : 0 < b) {r s : ℤ}
    (hr : 0 ≤ r ∧ r < b ∧ a ≡ r [ZMOD b])
    (hs : 0 ≤ s ∧ s < b ∧ a ≡ s [ZMOD b]) : r = s := by
  obtain ⟨hr1, hr2, ⟨p, hp⟩⟩ := hr
  obtain ⟨hs1, hs2, ⟨q, hq⟩⟩ := hs
  obtain ⟨k, hk⟩ : b ∣ r - s
  · use q - p
    calc r - s
      _ = a - b * p - (a - b * q) := by addarith [hp, hq]
      _ = b * (q - p) := by ring
  have hrs1 :=
    calc b * k
      _ = r - s := by rw [hk]
      _ < b - s := by addarith [hr2]
      _ ≤ b - s + s := by extra
      _ = b * 1 := by ring
  have hrs2 :=
    calc b * -1
      _ = -b := by ring
      _ < -s := by addarith [hs2]
      _ ≤ r - s := by extra
      _ = b * k := hk
  cancel b at hrs1
  cancel b at hrs2
  interval_cases k
  calc
    r = r - s + s := by ring
    _ = b * 0 + s := by rw [hk]
    _ = s := by ring

example (a b : ℤ) (h : 0 < b) : ∃! r : ℤ, 0 ≤ r ∧ r < b ∧ a ≡ r [ZMOD b] := by
  use fmod a b
  constructor
  · constructor
    · apply fmod_nonneg_of_pos _ h
    constructor
    · apply fmod_lt_of_pos _ h
    · use fdiv a b
      addarith [fmod_add_fdiv _ _]
  · intro r hr
    apply uniqueness a b h hr
    constructor
    · apply fmod_nonneg_of_pos _ h
    constructor
    · apply fmod_lt_of_pos _ h
    · use fdiv a b
      addarith [fmod_add_fdiv _ _]

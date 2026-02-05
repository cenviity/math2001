/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Basic

math2001_init

namespace Int


example : Odd 7 := by
  dsimp [Odd]
  use 3
  numbers


example : Odd (-3) := by
  use -2
  numbers

example {n : ℤ} (hn : Odd n) : Odd (3 * n + 2) := by
  dsimp [Odd] at *
  obtain ⟨k, hk⟩ := hn
  use 3 * k + 2
  calc
    3 * n + 2 = 3 * (2 * k + 1) + 2 := by rw [hk]
    _ = 2 * (3 * k + 2) + 1 := by ring


example {n : ℤ} (hn : Odd n) : Odd (7 * n - 4) := by
  obtain ⟨k, hk⟩ := hn
  use 7 * k + 1
  calc 7 * n - 4
    _ = 7 * (2 * k + 1) - 4 := by rw [hk]
    _ = 2 * (7 * k + 1) + 1 := by ring

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x + y + 1) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use a + b + 1
  calc
    x + y + 1 = 2 * a + 1 + (2 * b + 1) + 1 := by rw [ha, hb]
    _ = 2 * (a + b + 1) + 1 := by ring


example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y + 2 * y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use 2 * a * b + 3 * b + a + 1
  calc x * y + 2 * y
    _ = (2 * a + 1) * (2 * b + 1) + 2 * (2 * b + 1) := by rw [ha, hb]
    _ = 4 * a * b + 2 * a + 6 * b + 3 := by ring
    _ = 2 * (2 * a * b + 3 * b + a + 1) + 1 := by ring

example {m : ℤ} (hm : Odd m) : Even (3 * m - 5) := by
  obtain ⟨t, ht⟩ := hm
  use 3 * t - 1
  calc 3 * m - 5
    _ = 3 * (2 * t + 1) - 5 := by rw [ht]
    _ = 6 * t - 2 := by ring
    _ = 2 * (3 * t - 1) := by ring

example {n : ℤ} (hn : Even n) : Odd (n ^ 2 + 2 * n - 5) := by
  obtain ⟨k, hk⟩ := hn
  use 2 * k ^ 2 + 2 * k - 3
  calc n ^ 2 + 2 * n - 5
    _ = (2 * k) ^ 2 + 2 * (2 * k) - 5 := by rw [hk]
    _ = 4 * k ^ 2 + 4 * k - 5 := by ring
    _ = 2 * (2 * k ^ 2 + 2 * k - 3) + 1 := by ring

example (n : ℤ) : Even (n ^ 2 + n + 4) := by
  obtain hn | hn := even_or_odd n
  · obtain ⟨x, hx⟩ := hn
    use 2 * x ^ 2 + x + 2
    calc
      n ^ 2 + n + 4 = (2 * x) ^ 2 + 2 * x + 4 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + x + 2) := by ring
  · obtain ⟨x, hx⟩ := hn
    use 2 * x ^ 2 + 3 * x + 3
    calc
      n ^ 2 + n + 4 = (2 * x + 1) ^ 2 + (2 * x + 1) + 4 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + 3 * x + 3) := by ring

/-! # Exercises -/


example : Odd (-9) := by
  use -5
  numbers

example : Even 26 := by
  use 13
  numbers

example {m n : ℤ} (hm : Odd m) (hn : Even n) : Odd (n + m) := by
  obtain ⟨a, ha⟩ := hm
  obtain ⟨b, hb⟩ := hn
  use a + b
  calc n + m
    _ = 2 * b + (2 * a + 1) := by rw [ha, hb]
    _ = 2 * (a + b) + 1 := by ring

example {p q : ℤ} (hp : Odd p) (hq : Even q) : Odd (p - q - 4) := by
  obtain ⟨a, ha⟩ := hp
  obtain ⟨b, hb⟩ := hq
  use a - b - 2
  calc p - q - 4
    _ = 2 * a + 1 - 2 * b - 4 := by rw [ha, hb]
    _ = 2 * (a - b - 2) + 1 := by ring

example {a b : ℤ} (ha : Even a) (hb : Odd b) : Even (3 * a + b - 3) := by
  obtain ⟨m, hm⟩ := ha
  obtain ⟨n, hn⟩ := hb
  use 3 * m + n - 1
  calc 3 * a + b - 3
    _ = 3 * (2 * m) + (2 * n + 1) - 3 := by rw [hm, hn]
    _ = 2 * (3 * m + n - 1) := by ring

example {r s : ℤ} (hr : Odd r) (hs : Odd s) : Even (3 * r - 5 * s) := by
  obtain ⟨a, ha⟩ := hr
  obtain ⟨b, hb⟩ := hs
  use 3 * a - 5 * b - 1
  calc 3 * r - 5 * s
    _ = 3 * (2 * a + 1) - 5 * (2 * b + 1) := by rw [ha, hb]
    _ = 2 * (3 * a - 5 * b - 1) := by ring

example {x : ℤ} (hx : Odd x) : Odd (x ^ 3) := by
  obtain ⟨k, hk⟩ := hx
  use 4 * k ^ 3 + 6 * k ^ 2 + 3 * k
  calc x ^ 3
    _ = (2 * k + 1) ^ 3 := by rw [hk]
    _ = 2 * (4 * k ^ 3 + 6 * k ^ 2 + 3 * k) + 1 := by ring

example {n : ℤ} (hn : Odd n) : Even (n ^ 2 - 3 * n + 2) := by
  obtain ⟨k, hk⟩ := hn
  use 2 * k ^ 2 - k
  calc n ^ 2 - 3 * n + 2
    _ = (2 * k + 1) ^ 2 - 3 * (2 * k + 1) + 2 := by rw [hk]
    _ = 2 * (2 * k ^ 2 - k) := by ring

example {a : ℤ} (ha : Odd a) : Odd (a ^ 2 + 2 * a - 4) := by
  obtain ⟨k, hk⟩ := ha
  use 2 * k ^ 2 + 4 * k - 1
  calc a ^ 2 + 2 * a - 4
    _ = (2 * k + 1) ^ 2 + 2 * (2 * k + 1) - 4 := by rw [hk]
    _ = 2 * (2 * k ^ 2 + 4 * k - 1) + 1 := by ring

example {p : ℤ} (hp : Odd p) : Odd (p ^ 2 + 3 * p - 5) := by
  obtain ⟨k, hk⟩ := hp
  use 2 * k ^ 2 + 5 * k - 1
  calc p ^ 2 + 3 * p - 5
    _ = (2 * k + 1) ^ 2 + 3 * (2 * k + 1) - 5 := by rw [hk]
    _ = 2 * (2 * k ^ 2 + 5 * k - 1) + 1 := by ring

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use 2 * a * b + a + b
  calc x * y
    _ = (2 * a + 1) * (2 * b + 1) := by rw [ha, hb]
    _ = 2 * (2 * a * b + a + b) + 1 := by ring

example (n : ℤ) : Odd (3 * n ^ 2 + 3 * n - 1) := by
  obtain ⟨k, hk⟩ | ⟨k, hk⟩ := even_or_odd n
  · use 6 * k ^ 2 + 3 * k - 1
    calc 3 * n ^ 2 + 3 * n - 1
      _ = 3 * (2 * k) ^ 2 + 3 * (2 * k) - 1 := by rw [hk]
      _ = 2 * (6 * k ^ 2 + 3 * k - 1) + 1 := by ring
  · use 6 * k ^ 2 + 9 * k + 2
    calc 3 * n ^ 2 + 3 * n - 1
      _ = 3 * (2 * k + 1) ^ 2 + 3 * (2 * k + 1) - 1 := by rw [hk]
      _ = 2 * (6 * k ^ 2 + 9 * k + 2) + 1 := by ring

example (n : ℤ) : ∃ m ≥ n, Odd m := by
  obtain ⟨k, hk⟩ | ⟨k, hk⟩ := even_or_odd n
  · use 2 * k + 1
    constructor
    · calc 2 * k + 1
        _ = n + 1 := by rw [hk]
        _ ≥ n := by extra
    · use k
      ring
  · use n
    constructor
    · extra
    · use k
      apply hk

example (a b c : ℤ) : Even (a - b) ∨ Even (a + c) ∨ Even (b - c) := by
  obtain hab | hab := even_or_odd (a - b)
  · left
    apply hab
  · obtain hac | hac := even_or_odd (a + c)
    · right
      left
      apply hac
    · obtain ⟨m, hm⟩ := hab
      obtain ⟨n, hn⟩ := hac
      right
      right
      have habc : Even (a - b + (a + c))
      · use m + n + 1
        calc a - b + (a + c)
          _ = 2 * m + 1 + (2 * n + 1) := by rw [hm, hn]
          _ = 2 * (m + n + 1) := by ring
      · use a - m - n - 1
        calc b - c
          _ = 2 * a - (a - b + (a + c)) := by ring
          _ = 2 * a - (2 * m + 1 + (2 * n + 1)) := by rw [hm, hn]
          _ = 2 * (a - m - n - 1) := by ring

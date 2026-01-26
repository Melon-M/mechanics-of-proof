/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {a : ℚ} (h : ∃ b : ℚ, a = b ^ 2 + 1) : a > 0 := by
  obtain ⟨b, hb⟩ := h
  calc
    a = b ^ 2 + 1 := hb
    _ > 0 := by extra


example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  obtain ⟨x, hxt⟩ := h
  have H := le_or_gt x 0
  obtain hx | hx := H
  · have hxt' : 0 < (-x) * t := by addarith [hxt]
    have hx' : 0 ≤ -x := by addarith [hx]
    cancel -x at hxt'
    apply ne_of_gt
    apply hxt'
<<<<<<< HEAD
  · have hxt' : 0 < x * (-t) := by
      calc
        0 < -x * t := by addarith[hxt]
        _ = x * (-t) := by ring
    cancel x at hxt'
    apply ne_of_lt
    addarith [hxt']
=======
  · have h1 : 0 < x * -t := by
      calc
        0 < -x * t := by addarith [hxt]
        _ = x * (-t) := by ring
    have h2 : 0 < -t := by cancel x at h1
    have h3 : t < 0 := by addarith [h2]
    apply ne_of_lt
    apply h3
>>>>>>> 7235ef88f2780bf351bea3ceef58e0e78695f2a1


example : ∃ n : ℤ, 12 * n = 84 := by
  use 7
  numbers


example (x : ℝ) : ∃ y : ℝ, y > x := by
  use x + 1
  extra


example : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 11 := by
  use 6
  use 5
<<<<<<< HEAD
  ring

example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use (a + 1)
=======
  numbers

example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use a + 1
>>>>>>> 7235ef88f2780bf351bea3ceef58e0e78695f2a1
  use a
  ring

example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p + q) / 2
  constructor
  · calc
      p = (p + p) / 2 := by ring
<<<<<<< HEAD
      _ < (p + q) / 2 := by addarith [h]
  · calc
      (p + q) / 2 < (q + q) / 2 := by addarith [h]
      _ = q := by ring
=======
      _ < (p + q) / 2 := by rel [h]
  · calc
      q = (q + q) / 2 := by ring
      _ > (p + q) / 2 := by rel [h]
>>>>>>> 7235ef88f2780bf351bea3ceef58e0e78695f2a1

example : ∃ a b c d : ℕ,
    a ^ 3 + b ^ 3 = 1729 ∧ c ^ 3 + d ^ 3 = 1729 ∧ a ≠ c ∧ a ≠ d := by
  use 1, 12, 9, 10
  constructor
  numbers
  constructor
  numbers
  constructor
  numbers
  numbers

/-! # Exercises -/


example : ∃ t : ℚ, t ^ 2 = 1.69 := by
  use 1.3
  numbers

example : ∃ m n : ℤ, m ^ 2 + n ^ 2 = 85 := by
  use 7; use 6
  numbers

example : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by
  use -0.5
  constructor
  · numbers
  · numbers

example : ∃ a b : ℕ, 2 ^ a = 5 * b + 1 := by
  use 4; use 3
  numbers

example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  have H := lt_or_ge x 0
  obtain hx | hx := H
  · use x
    calc
       x ^ 2 ≥ 0 := by apply sq_nonneg
       _ > x := by rel [hx]
  · use (x + 1)
    calc
      (x + 1) ^ 2 = x ^ 2 + x + x + 1 := by ring
      _ >= x + x + 1 := by extra
      _ > x + x := by extra
      _ >= x := by extra

example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  obtain ⟨a, ha⟩ := h
  have h1 : (a - 1) * (t - 1) ≠ 0 := by
    apply ne_of_lt
    calc
      (a - 1) * (t - 1) = (a * t + 1) - a - t := by ring
      _ < (a + t) - a - t := by rel [ha]
      _ = 0 := by ring
  have h2 : (t - 1) ≠ 0 := right_ne_zero_of_mul h1
  apply sub_ne_zero.mp h2

example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  sorry

example {n : ℤ} : ∃ a, 2 * a ^ 3 ≥ n * a + 7 := by
  sorry

example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by
  sorry

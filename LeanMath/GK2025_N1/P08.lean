import LeanMath.Utils.BasicAlgebra.Notations
import LeanMath.Utils.Kickstart

import Mathlib.Analysis.SpecialFunctions.Log.Base

open Utils.Kickstart
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.multiGoal false

-- Problems 1 to 8 are single-choice questions.
-- This file contains problem 8.
namespace GK2025_N1

/-! **Problem 8**: Given `2 + log_2 x = 3 + log_3 y = 5 + log_5 z`, then the order of
  `x, y, z` must NOT be ( ? ) -/
namespace P08
open Real
open Utils.BasicAlgebra

-- Weirdly, the `log` function (like division) has "junk values" in Mathlib to make it total,
-- which contradicts with common mathematical practice.
-- Effectively, Mathlib users become responsible for explicitly stating the domain of `log`
-- when using it, which is a bit of a hassle. Shrug...
abbrev condition (x y z : ℝ>0) :=
  2 + logb 2 x = 3 + logb 3 y ∧
                 3 + logb 3 y = 5 + logb 5 z

-- Let's start to solve this problem.
-- Although we have 3 unknowns `x, y, z`, they only have degree of freedom (DoF) = 1.
-- Hence, let `k = 2 + log_2 x`, then all of `x, y, z` can be represented with `k`.

-- Since the way to find `x, y, z` with `k` is similar, let's solve a single sub-problem:
#count_heartbeats in
noncomputable def sub_problem (k : ℝ) (x : ℝ>0) {a? b? : ℝ} (hb? : (b? > 0 ∧ b? ≠ 1))
    (eqn : k = a? + logb b? x)
    : find_one { _? | (x : ℝ) = _? } := by
  apply_fun (· - a?) at eqn; simp at eqn  -- minus a? on both sides
  symm at eqn; rewrite [logb_eq_iff_rpow_eq] at eqn  -- convert logb equation to pow equation
    <;> try grind
  answer! b? ^ (k - a?)
  grind

lemma x_of_k {x : ℝ>0} {k} (hk : k = 2 + logb 2 x) : (x : ℝ) = 2 ^ (k - 2) := by
  reuse! 2 ^ (k - 2) from (sub_problem k x (by norm_num) hk) as h; grind

lemma y_of_k {y : ℝ>0} {k} (hk : k = 3 + logb 3 y) : (y : ℝ) = 3 ^ (k - 3) := by
  reuse! 3 ^ (k - 3) from (sub_problem k y (by norm_num) hk) as h; grind

lemma z_of_k {z : ℝ>0} {k} (hk : k = 5 + logb 5 z) : (z : ℝ) = 5 ^ (k - 5) := by
  reuse! 5 ^ (k - 5) from (sub_problem k z (by norm_num) hk) as h; grind

-- Aha! Since `x = 2 ^ (k - 2)` (similar for `y` and `z`), we have `ln x = (ln 2) * (k - 2)`.
-- "Visually thinking", point `(k, ln x)` forms a *straight line* (in a 2D Euclidian space);
--   similarly, `y` / `z` also makes a straight line.
-- With 3 straight lines, there could be 4 different orders of `x, y, z` at most.
-- We're not asked to prove this, but this is a helpful mental picture to solve this problem!

-- Since we're to choose an option that MUST be false,
--   we only need to figure out a *strong-enough* *invariant*,
--   which is a predicate on `x, y, z` that holds for any `k`.
-- How to choose our invariant? Let's start with some calculation!

/-- info: [0.250000, 0.500000, 1.000000, 2.000000, 4.000000, 8.000000, 16.000000] -/
#guard_msgs in
#eval (List.range 7).map fun k => 2 ^ (k.toFloat - 2)  -- for `x`

/-- info: [0.037037, 0.111111, 0.333333, 1.000000, 3.000000, 9.000000, 27.000000] -/
#guard_msgs in
#eval (List.range 7).map fun k => 3 ^ (k.toFloat - 3)  -- for `y`

/-- info: [0.000320, 0.001600, 0.008000, 0.040000, 0.200000, 1.000000, 5.000000] -/
#guard_msgs in
#eval (List.range 7).map fun k => 5 ^ (k.toFloat - 5)  -- for `z`

-- Aha! Imagine how the order of `x, y, z` changes as `k` increases?
-- 1. Initially, `z` is the smallest; `x > y` at first, but then (when `k ≥ 5`), `y > x`.
-- 2. When `k = 5`, `z` is still the smallest, but eventually `z` will become the largest.
-- Notice how this covers *all* 4 different orders, so such an invariant is *strong enough*.

-- Got it! Below is the invariant:
#count_heartbeats in
lemma invariant {x y z : ℝ>0} {k : ℝ}
    (hx : (x : ℝ) = 2 ^ (k - 2)) (hy : (y : ℝ) = 3 ^ (k - 3)) (hz : (z : ℝ) = 5 ^ (k - 5))
    : (z < x ∧ z < y) ∨ (x < y) := by
  repeat rw [← Subtype.coe_lt_coe]  -- convert `x, y, z` into `↑x, ↑y, ↑z`
  rw [hx, hy, hz]
  by_cases hk : k < 5
  · left  -- case `k < 5`
    have h_common (b? : ℝ) (hb? : 1 < b? ∧ b? < 5) : 5 ^ (k - 5) < b? ^ (k - b?) := by
      calc 5 ^ (k - 5)
       _ < b? ^ (k - 5)   := by grind [rpow_lt_rpow_of_neg]
       _ < b? ^ (k - b?)  := by grind [rpow_lt_rpow_of_exponent_lt]
    grind [h_common 2, h_common 3]
  · right  -- case `k ≥ 5`
    calc (2 : ℝ) ^ (k - 2)
     _ = (2 : ℝ) ^ (k - 5) * 8  := by
                                rw [show (8 : ℝ) = 2 ^ (3 : ℝ) by norm_num]
                                rw [← rpow_add (by norm_num)]; grind
     _ < (3 : ℝ) ^ (k - 5) * 9  := by
                                apply mul_lt_mul' <;> try grind
                                · apply rpow_le_rpow <;> grind
                                · positivity
     _ = (3 : ℝ) ^ (k - 3)      := by
                                rw [show (9 : ℝ) = 3 ^ (2 : ℝ) by norm_num]
                                rw [← rpow_add (by norm_num)]; grind

-- Now essentially we have figured out the main problem!

-- It is preferred to model such problems within set theory, which has maximal flexibility
-- in specifying "must/may (not) be", "has exactly one/two/more" kinds of stuff.
#count_heartbeats in
def problem : choose_one { _? | { (x, y, z) | condition x y z } ∩ _? = ∅ } (match · with
  | Choice.A => { (x, y, z) : ℝ>0 × ℝ>0 × ℝ>0 | x > y ∧ y > z }
  | Choice.B => { (x, y, z) : ℝ>0 × ℝ>0 × ℝ>0 | x > z ∧ z > y }
  | Choice.C => { (x, y, z) : ℝ>0 × ℝ>0 × ℝ>0 | y > x ∧ x > z }
  | Choice.D => { (x, y, z) : ℝ>0 × ℝ>0 × ℝ>0 | y > z ∧ z > x }) := by
  -- The invariant says: either `z` is smallest (as in `Choice.A` and `Choice.C`),
  -- or `y > x` (as in `Choice.D`).
  answer! Choice.B
  simp; rw [Set.eq_empty_iff_forall_notMem]; rintro ⟨x, y, z⟩; simp
  rintro hxy hyz
  let k := 2 + logb 2 x
  have hx := x_of_k (show k = 2 + logb 2 x by grind)
  have hy := y_of_k (show k = 3 + logb 3 y by grind)
  have hz := z_of_k (show k = 5 + logb 5 z by grind)
  have h_inv := invariant hx hy hz
  grind

end P08

end GK2025_N1

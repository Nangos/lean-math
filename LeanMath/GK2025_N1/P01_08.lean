import LeanMath.Utils.BasicAlgebra.Function
import LeanMath.Utils.Kickstart

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic

open Utils.Kickstart
set_option linter.style.multiGoal false

-- Problems 1 to 8 are single-choice questions.
namespace GK2025_N1

/-! Problem 1: The imaginary part of `(1 + 5i) i` is ( ? ) !-/
namespace P01
open Complex

#count_heartbeats in
def problem : choose_one { _? | ((1 + 5 * I) * I).im = _? } (match · with
  | Choice.A => -1
  | Choice.B => 0
  | Choice.C => 1
  | Choice.D => 6) := by
  start!
  simp  -- easiest warm-up problem, just plain computation
  answer! Choice.C
  rfl
end P01

/-! Problem 2: Let `U = {x | x is a positive integer less than 9}` and `A = {1, 3, 5}`.
  The number of elements in `U \ A` is ( ? ) -/
namespace P02

def U : Set ℤ := { x | x > 0 ∧ x < 9 }
def A : Set ℤ := {1, 3, 5}

-- The choices assume (U \ A) is finite, but we must be explicit in Lean.
#count_heartbeats in
def problem : choose_one { _? | (U \ A).Finite ∧ (U \ A).ncard = _? } (match · with
  | Choice.A => 0
  | Choice.B => 3
  | Choice.C => 5
  | Choice.D => 8) := by
  start!
  simp [U, A]
  rw [← Set.Ioo]  -- `Ioo` stands for "Interval Open-Open". This transforms U.
  simp  -- The finiteness is automatically proved!
  -- Next let's compute the cardinality.
  rw [Set.ncard_diff (by grind)]  -- |U \ A| = |U| - |A|, since A ⊆ U.
  rw [← Finset.coe_Ioo, Set.ncard_coe_finset]  -- boilerplate, cast U as a finset
  simp  -- now LHS can be reduced to a number!
  answer! Choice.C
  rfl
end P02

/-! Problem 3: The length of the conjugate axis of the hyperbola `C` is `√7` times that of
  its transverse axis. Then the eccentricity of `C` is ( ? ) -/
namespace P03
-- TODO: Pending the geometry library...
end P03

/-! Problem 5: Given that `f (x : ℝ) : ℝ` is an even function with a period of 2, and that
  `f(x) = 5-2x` for `2 ≤ x ≤ 3`, then `f(-3/4)` equals ( ? ) -/
namespace P05
open Utils.BasicAlgebra

abbrev condition (f : ℝ → ℝ) :=
  isEven f ∧ hasPeriod f 2 ∧ (∀ x, 2 ≤ x ∧ x ≤ 3 → f x = 5 - 2 * x)

-- TODO: This subtlety first arises in P03, update this comment when P03 is done.
-- Fairly, there is no apparent evidence that the given condition determines a unique `f`
-- or in particular a unique value of `f (-3/4)`. A well-formed problem should ask for the
-- set of all possible values instead.
-- However, since this is a single-choice question, we will interpret problems like this as
-- asserting a unique answer exists for all possible `f`s.
#count_heartbeats in
def problem : choose_one { _? | ∀ f, condition f → f (-3/4) = _? } (match · with
  | Choice.A => -1/2
  | Choice.B => -1/4
  | Choice.C => 1/4
  | Choice.D => 1/2) := by
  start!
  simp [isEven, hasPeriod]
  rintro f hEven hPeriodOf2 hPartialDef
  norm_num  -- imporantly reduces (-3)/4 to -(3/4)!!
  rw [hEven]  -- f (-3/4) = f (3/4)
  rw [← hPeriodOf2]  -- f (3/4) = f (3/4 + 2), got in the [2, 3] range!!
  rw [hPartialDef _ (by linarith) (by linarith)]; norm_num  -- plug in; simplify!
  answer! Choice.A
  rfl
end P05

/-! Problem 8: Given `2 + log_2 x = 3 + log_3 y = 5 + log_5 z`, then the order of `x, y, z`
  must NOT be ( ? ) -/
namespace P08
open Real

-- Weirdly, the `log` function (like division) has "junk values" in Mathlib to make it total,
-- which contradicts with common mathematical practice.
-- Effectively, Mathlib users become responsible for explicitly stating the domain of `log`
-- when using it, which is a bit of a hassle. Shrug...
structure Vars where
  (x y z : ℝ)
  (valid : 0 < x ∧ 0 < y ∧ 0 < z)

abbrev condition (vars : Vars) :=
  let {x, y, z, ..} := vars
  2 + logb 2 x = 3 + logb 3 y ∧
                 3 + logb 3 y = 5 + logb 5 z

-- It is preferred to model such problems within set theory, which has maximal flexibility
-- in specifying "must/may (not) be", "has exactly one/two/more" kinds of stuff.
#count_heartbeats in
def problem : choose_one { _? | { vars | condition vars } ∩ _? = ∅ } (match · with
  | Choice.A => { {x, y, z, ..} : Vars | x > y ∧ y > z }
  | Choice.B => { {x, y, z, ..} : Vars | x > z ∧ z > y }
  | Choice.C => { {x, y, z, ..} : Vars | y > x ∧ x > z }
  | Choice.D => { {x, y, z, ..} : Vars | y > z ∧ z > x }) := by
  sorry
end P08

end GK2025_N1

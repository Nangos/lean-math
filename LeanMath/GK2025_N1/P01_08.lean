import LeanMath.Utils.Kickstart
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic

open Utils.Kickstart
set_option linter.style.multiGoal false

-- Problems 1 to 8 are single-choice questions.
namespace GK2025_N1

-- Problem 1: The imaginary part of `(1 + 5i) i` is ( ? )
namespace P01
open Complex

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

-- Problem 2: Let `U = {x | x is a positive integer less than 9}` and `A = {1, 3, 5}`.
-- The number of elements in `U \ A` is ( ? )
namespace P02

def U : Set ℤ := { x | x > 0 ∧ x < 9 }
def A : Set ℤ := {1, 3, 5}

-- The choices assume (U \ A) is finite, but we must be explicit in Lean.
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

-- Problem 3: The length of the conjugate axis of the hyperbola `C` is `√7` times that of
-- its transverse axis. Then the eccentricity of `C` is ( ? )
namespace P03
-- TODO: Pending the geometry library...
end P03

end GK2025_N1

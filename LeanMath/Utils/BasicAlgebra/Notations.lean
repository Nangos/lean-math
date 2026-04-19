import Mathlib.Tactic

/-! Some convenience notations for algebraic problem solving. -/

namespace Utils.BasicAlgebra

/-- Positive real number. -/
abbrev PosReal := { x : ℝ // x > 0 }
scoped notation "ℝ>0" => PosReal

/-- Negative real number. -/
abbrev NegReal := { x : ℝ // x < 0 }
scoped notation "ℝ<0" => NegReal

/-- Non-negative real number. -/
abbrev NonNegReal := { x : ℝ // x ≥ 0 }
scoped notation "ℝ≥0" => NonNegReal

/-- Non-positive real number. -/
abbrev NonPosReal := { x : ℝ // x ≤ 0 }
scoped notation "ℝ≤0" => NonPosReal

/-- Non-zero real number. -/
abbrev NonZeroReal := { x : ℝ // x ≠ 0 }
scoped notation "ℝ≠0" => NonZeroReal

end Utils.BasicAlgebra

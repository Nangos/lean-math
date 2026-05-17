import LeanMath.Utils.BasicGeometry.Common

open Real

namespace Utils.BasicGeometry

/-- Internal representation of a 2D hyperbola,
providing various parameterized construction methods. -/
inductive Hyperbola2D.internal
  | /-- A classic hyperbola defined by two distinct foci and a constant difference in distances.
    `valid` ensures it's a non-degenerate hyperbola (0 < d_diff < 2c). -/
    FociDiff (F₁ F₂ : Point 2) (d_diff : ℝ) (valid : 0 < d_diff ∧ d_diff < dist F₁ F₂)
  | /-- A hyperbola centered at origin under a certain coordinate system, defined by semi-major
    and semi-minor axes a and b. -/
    CoordAxes (Φ : CoordSys 2) (a b : ℝ) (valid : 0 < a ∧ 0 < b)

/-- Evaluates the internal representation into a standard set of points. -/
def Hyperbola2D.internal.toPointSet : Hyperbola2D.internal → Set (Point 2)
  | FociDiff F₁ F₂ d_diff _ => { p | |dist p F₁ - dist p F₂| = d_diff }
  | CoordAxes Φ a b _ => { p | ((Φ p 0)^2 / a^2) - ((Φ p 1)^2 / b^2) = 1 }

/-- An equivalence relation for internal hyperbolas: equivalent if their point sets are equal. -/
instance Hyperbola2D.setoid : Setoid Hyperbola2D.internal where
  r h1 h2 := h1.toPointSet = h2.toPointSet
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h1 h2 => Eq.trans h1 h2
  }

/-- A hyperbola in 2-dimensional space, defined as a quotient type over the point set
equivalence relation. -/
abbrev Hyperbola2D := Quotient Hyperbola2D.setoid

/-- Constructs a hyperbola from two foci and the distance difference. -/
def Hyperbola2D.ofFociDiff (F₁ F₂ : Point 2) (d_diff : ℝ)
    (valid : 0 < d_diff ∧ d_diff < dist F₁ F₂) : Hyperbola2D :=
  Quotient.mk _ (Hyperbola2D.internal.FociDiff F₁ F₂ d_diff valid)

/-- Extracts the set of points representing the hyperbola. -/
def Hyperbola2D.toPointSet (h : Hyperbola2D) : PointSet 2 :=
  Quotient.lift Hyperbola2D.internal.toPointSet (fun _ _ h => h) h

instance : ToPointSet 2 Hyperbola2D := ⟨Hyperbola2D.toPointSet⟩

/-- Constructs a hyperbola from `p.x^2 / a^2 - p.y^2 / b^2 = 1` in coordinate system `Φ`. -/
def Hyperbola2D.fromFormulaAB {Φ : CoordSys 2} {a b : ℝ} (formula : PointViewSet Φ)
    (_h : formula = { p : PointView Φ | p.x^2 / a^2 - p.y^2 / b^2 = 1 } := by rfl)
    (valid : 0 < a ∧ 0 < b := by norm_num)
    : Hyperbola2D :=
  Quotient.mk _ (Hyperbola2D.internal.CoordAxes Φ a b valid)

/-- Asserts the consistency of the `Hyperbola2D.fromFormulaAB` construction. -/
theorem Hyperbola2D.fromFormulaAB_view_consistent {Φ : CoordSys 2} {a b : ℝ}
    (formula : PointViewSet Φ)
    (_h : formula = { p : PointView Φ | p.x^2 / a^2 - p.y^2 / b^2 = 1 })
    (valid : 0 < a ∧ 0 < b)
    : (Hyperbola2D.fromFormulaAB formula _h valid).toPointSet.view Φ = formula := by
  sorry

example {Φ : CoordSys 2} :
    (Hyperbola2D.fromFormulaAB
      { p : PointView Φ | p.x^2 / 2^2 - p.y^2 / 3^2 = 1 }).toPointSet.view Φ
    = { p | p.x^2 / 2^2 - p.y^2 / 3^2 = 1 } := by
  rw [Hyperbola2D.fromFormulaAB_view_consistent]

noncomputable def Hyperbola2D.internal.c : Hyperbola2D.internal → ℝ
  | FociDiff F₁ F₂ _ _ => dist F₁ F₂ / 2
  | CoordAxes _ a b _ => √(a^2 + b^2)

noncomputable def Hyperbola2D.internal.a : Hyperbola2D.internal → ℝ
  | FociDiff _ _ d_diff _ => d_diff / 2
  | CoordAxes _ a _ _ => a

noncomputable def Hyperbola2D.internal.b : Hyperbola2D.internal → ℝ
  | FociDiff F₁ F₂ d_diff _ => √((dist F₁ F₂ / 2)^2 - (d_diff / 2)^2)
  | CoordAxes _ _ b _ => b

noncomputable def Hyperbola2D.a (h : Hyperbola2D) : ℝ :=
  Quotient.lift Hyperbola2D.internal.a (by sorry) h

noncomputable def Hyperbola2D.b (h : Hyperbola2D) : ℝ :=
  Quotient.lift Hyperbola2D.internal.b (by sorry) h

noncomputable def Hyperbola2D.c (h : Hyperbola2D) : ℝ :=
  Quotient.lift Hyperbola2D.internal.c (by sorry) h

/-- Eccentricity of the hyperbola, always > 1. -/
noncomputable def Hyperbola2D.eccentricity (h : Hyperbola2D) : ℝ :=
  h.c / h.a

end Utils.BasicGeometry

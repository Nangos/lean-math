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
    CoordAxes (Φ : CoordSys 2) (h_iso : Isometry Φ) (a b : ℝ) (valid : 0 < a ∧ 0 < b)

/-- Evaluates the internal representation into a standard set of points. -/
def Hyperbola2D.internal.toPointSet : Hyperbola2D.internal → Set (Point 2)
  | FociDiff F₁ F₂ d_diff _ => { p | |dist p F₁ - dist p F₂| = d_diff }
  | CoordAxes Φ _ a b _ => { p | ((Φ p 0)^2 / a^2) - ((Φ p 1)^2 / b^2) = 1 }

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
def Hyperbola2D.fromFormulaAB {Φ : CoordSys 2} (h_iso : Isometry Φ) {a b : ℝ}
    (formula : PointViewSet Φ)
    (_h : formula = { p : PointView Φ | p.x^2 / a^2 - p.y^2 / b^2 = 1 } := by rfl)
    (valid : 0 < a ∧ 0 < b := by norm_num)
    : Hyperbola2D :=
  Quotient.mk _ (Hyperbola2D.internal.CoordAxes Φ h_iso a b valid)

/-- Asserts the consistency of the `Hyperbola2D.fromFormulaAB` construction. -/
theorem Hyperbola2D.fromFormulaAB_view_consistent {Φ : CoordSys 2} (h_iso : Isometry Φ)
    {a b : ℝ} (formula : PointViewSet Φ)
    (_h : formula = { p : PointView Φ | p.x^2 / a^2 - p.y^2 / b^2 = 1 })
    (valid : 0 < a ∧ 0 < b)
    : (Hyperbola2D.fromFormulaAB h_iso formula _h valid).toPointSet.view Φ = formula := by
  subst _h
  ext p
  dsimp [PointViewSet, PointSet.view, PointView.x, PointView.y, PointView.coord,
         Hyperbola2D.fromFormulaAB, Hyperbola2D.toPointSet]
  rfl

example {Φ : CoordSys 2} (h_iso : Isometry Φ) :
    (Hyperbola2D.fromFormulaAB h_iso
      { p : PointView Φ | p.x^2 / 2^2 - p.y^2 / 3^2 = 1 }).toPointSet.view Φ
    = { p | p.x^2 / 2^2 - p.y^2 / 3^2 = 1 } := by
  rw [Hyperbola2D.fromFormulaAB_view_consistent]

/-- Calculates the geometric center of the internal hyperbola representation. -/
noncomputable def Hyperbola2D.internal.center : Hyperbola2D.internal → Point 2
  | FociDiff F₁ F₂ _ _ => AffineMap.lineMap F₁ F₂ (1 / 2 : ℝ)
  | CoordAxes Φ _ _ _ _ => Φ.symm 0

/-- A geometric definition of a symmetry center for a point set.
A point C is a center of symmetry for S if reflecting any point in S across C keeps it in S. -/
def is_symmetry_center (S : Set (Point 2)) (C : Point 2) : Prop :=
  ∀ P, P ∈ S ↔ (AffineMap.lineMap C P (-1 : ℝ)) ∈ S

/-- Coordinates of reflected points are inverted when origin is the reflection center. -/
lemma symm_keeps_coord_axes (Φ : CoordSys 2) (a b : ℝ) (P : Point 2) :
  let C := Φ.symm 0;
  let P' := AffineMap.lineMap C P (-1 : ℝ);
  (Φ P' 0)^2 / a^2 - (Φ P' 1)^2 / b^2 = (Φ P 0)^2 / a^2 - (Φ P 1)^2 / b^2 := by
  intros C P'
  have hP' : Φ P' = - Φ P := by
    dsimp [P', C]
    rw [AffineEquiv.apply_lineMap]
    simp [AffineMap.lineMap_apply]
  rw [hP']
  simp

/-- Distances to foci are swapped when a point is reflected across the midpoint of the foci. -/
lemma dist_symm_foci (F₁ F₂ P : Point 2) :
    let C := AffineMap.lineMap F₁ F₂ (1 / 2 : ℝ)
    let P' := AffineMap.lineMap C P (-1 : ℝ)
    dist P' F₁ = dist P F₂ ∧ dist P' F₂ = dist P F₁ := by
  intros C P'
  dsimp [P', C]
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  have h1 : ∀ A B : Point 2, dist A B = ‖A - B‖ := dist_eq_norm
  simp only [h1]
  constructor
  · rw [← norm_neg (P - F₂)]
    congr 1
    ext i
    change (-1 • (P - ((1 / 2 : ℝ) • (F₂ - F₁) + F₁)) +
      ((1 / 2 : ℝ) • (F₂ - F₁) + F₁) - F₁) i = (-(P - F₂)) i
    simp [smul_eq_mul]
    ring
  · rw [← norm_neg (P - F₁)]
    congr 1
    ext i
    change (-1 • (P - ((1 / 2 : ℝ) • (F₂ - F₁) + F₁)) +
      ((1 / 2 : ℝ) • (F₂ - F₁) + F₁) - F₂) i = (-(P - F₁)) i
    simp [smul_eq_mul]
    ring

/-- Any hyperbola point set has exactly one center of symmetry. -/
lemma symmetry_center_is_unique (S : Set (Point 2)) (C₁ C₂ : Point 2)
    (hS : ∃ h : Hyperbola2D.internal, h.toPointSet = S)
    (h₁ : is_symmetry_center S C₁)
    (h₂ : is_symmetry_center S C₂) : C₁ = C₂ := by
  sorry

/-- The internal center is a valid symmetry center for the hyperbola's point set. -/
lemma internal_center_is_symmetry_center (h : Hyperbola2D.internal) :
    is_symmetry_center h.toPointSet h.center := by
  intro P
  cases h with
  | FociDiff F₁ F₂ d_diff valid =>
    dsimp [Hyperbola2D.internal.toPointSet, Hyperbola2D.internal.center]
    have h_symm := dist_symm_foci F₁ F₂ P
    rw [h_symm.1, h_symm.2]
    exact abs_sub_comm (dist P F₂) (dist P F₁) ▸ Iff.rfl
  | CoordAxes Φ _ a b valid =>
    dsimp [Hyperbola2D.internal.toPointSet, Hyperbola2D.internal.center]
    have h_symm := symm_keeps_coord_axes Φ a b P
    rw [h_symm]

/-- Therefore, the center is an invariant of the point set. -/
lemma center_invariant {h1 h2 : Hyperbola2D.internal}
    (heq : h1.toPointSet = h2.toPointSet) :
    h1.center = h2.center := by
  apply symmetry_center_is_unique h1.toPointSet _ _ ⟨h1, rfl⟩
  · exact internal_center_is_symmetry_center h1
  · rw [heq]
    exact internal_center_is_symmetry_center h2

/-- The geometric center of the hyperbola. Well-definedness is guaranteed by
the unique symmetry center property. -/
noncomputable def Hyperbola2D.center (h : Hyperbola2D) : Point 2 :=
  Quotient.lift Hyperbola2D.internal.center (fun _ _ heq => center_invariant heq) h

/-- Calculates the semi-major axis `a` from the internal representation. -/
noncomputable def Hyperbola2D.internal.a : Hyperbola2D.internal → ℝ
  | FociDiff _ _ d_diff _ => d_diff / 2
  | CoordAxes _ _ a _ _ => a

/-- The semi-major axis `a` can be characterized geometrically as the infimum of the distance
from the center to any point on the hyperbola. -/
lemma internal_a_is_min_distance (h : Hyperbola2D.internal) :
    h.a = sInf (dist h.center '' h.toPointSet) := by
  sorry

/-- Therefore, `a` is an invariant of the point set. -/
lemma a_invariant {h1 h2 : Hyperbola2D.internal}
    (heq : h1.toPointSet = h2.toPointSet) :
    h1.a = h2.a := by
  rw [internal_a_is_min_distance h1, internal_a_is_min_distance h2]
  have hc : h1.center = h2.center := center_invariant heq
  rw [hc, heq]

/-- The semi-major axis `a` of the hyperbola. Well-definedness is guaranteed by
its correlation with the invariant distance infimum from the center. -/
noncomputable def Hyperbola2D.a (h : Hyperbola2D) : ℝ :=
  Quotient.lift Hyperbola2D.internal.a (fun _ _ heq => a_invariant heq) h

-- We will implement b and c later based on characteristic features.
-- noncomputable def Hyperbola2D.internal.c : Hyperbola2D.internal → ℝ
--   | FociDiff F₁ F₂ _ _ => dist F₁ F₂ / 2
--   | CoordAxes _ a b _ => √(a^2 + b^2)

-- noncomputable def Hyperbola2D.internal.b : Hyperbola2D.internal → ℝ
--   | FociDiff F₁ F₂ d_diff _ => √((dist F₁ F₂ / 2)^2 - (d_diff / 2)^2)
--   | CoordAxes _ _ b _ => b

-- noncomputable def Hyperbola2D.b (h : Hyperbola2D) : ℝ :=
--   Quotient.lift Hyperbola2D.internal.b (by sorry) h

-- noncomputable def Hyperbola2D.c (h : Hyperbola2D) : ℝ :=
--   Quotient.lift Hyperbola2D.internal.c (by sorry) h

-- /-- Eccentricity of the hyperbola, always > 1. -/
-- noncomputable def Hyperbola2D.eccentricity (h : Hyperbola2D) : ℝ :=
--   h.c / h.a

end Utils.BasicGeometry

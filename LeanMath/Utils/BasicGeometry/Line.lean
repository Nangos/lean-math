import LeanMath.Utils.BasicGeometry.Common

namespace Utils.BasicGeometry

/-- Internal representation of a line, providing various parameterized construction methods. -/
inductive Line.internal (n : ℕ)
  | /-- A line determined by two distinct points. -/
    Point2 (p₁ p₂ : Point n) (valid : p₁ ≠ p₂)

/-- Evaluates the internal representation of a line into a standard set of points. -/
def Line.internal.toPointSet {n : ℕ} : Line.internal n → Set (Point n)
  | Point2 p₁ p₂ _ => { p | ∃ (t : ℝ), p = (1 - t) • p₁ + t • p₂ }

/-- An equivalence relation for internal lines: two internal representations are equivalent
if their corresponding point sets are equal. -/
instance Line.setoid (n : ℕ) : Setoid (Line.internal n) where
  r l1 l2 := l1.toPointSet = l2.toPointSet
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h1 h2 => Eq.trans h1 h2
  }

/-- A straight line in n-dimensional space, defined as a quotient type over the point set
equivalence relation. -/
def Line (n : ℕ) := Quotient (Line.setoid n)

/-- Constructs a line passing through two distinct points. -/
def Line.ofPoint2 {n : ℕ} (p₁ p₂ : Point n) (valid : p₁ ≠ p₂) : Line n :=
  Quotient.mk _ (Line.internal.Point2 p₁ p₂ valid)

/-- Extracts the set of points representing the line. It safely lifts the operation over the
quotient type because the equivalence relation preserves the point set. -/
def Line.toPointSet {n : ℕ} (l : Line n) : PointSet n :=
  Quotient.lift Line.internal.toPointSet (fun _ _ h => h) l

/-- Instantiates `Line n` as a `PointSet`, allowing its treating as a set of points. -/
instance {n : ℕ} : ToPointSet n (Line n) := ⟨Line.toPointSet⟩


/-- A line in 2-dimensional space (a.k.a. in a plane). -/
abbrev Line2D := Line 2

/-- Constructs a Line2D from a slope `k` and y-intercept `y₀` in coordinate system `Φ`:
`{ p | p.y = k * p.x + y₀ }`. -/
def Line2D.fromSlopeY {Φ : CoordSys 2} {k y₀ : ℝ} (formula : PointViewSet Φ)
    (_h : formula = { p : PointView Φ | p.y = k * p.x + y₀ } := by rfl) : Line2D :=
  -- The line passes through points (0, y₀) and (1, k + y₀).
  Line.ofPoint2 (Φ.symm ![0, y₀]) (Φ.symm ![1, k + y₀]) (by
    intro h
    have h_coord := congrArg Φ h
    simp only [Equiv.apply_symm_apply] at h_coord
    have h_zero : (0 : ℝ) = 1 := by
      calc (0 : ℝ)
       _ = (![0, y₀] : Fin 2 → ℝ) 0 := rfl
       _ = (![1, k + y₀] : Fin 2 → ℝ) 0 := congrFun h_coord 0
       _ = 1 := rfl
    norm_num at h_zero)

/-- Asserts the consistency of the `Line2D.fromSlopeY` construction. Namely, the resulting line
has the expected point set in the given coordinate system. -/
theorem Line2D.fromSlopeY_view_consistent {Φ : CoordSys 2} {k y₀ : ℝ} (formula : PointViewSet Φ)
    (_h : formula = { p : PointView Φ | p.y = k * p.x + y₀ } := by rfl) :
    (Line2D.fromSlopeY formula _h).toPointSet.view Φ = formula := by
  sorry

example {Φ : CoordSys 2} :
    (Line2D.fromSlopeY { p : PointView Φ | p.y = 2 * p.x - 3 }).toPointSet.view Φ
    = { p | p.y = 2 * p.x - 3 } := by
  simp [Line2D.fromSlopeY_view_consistent]

end Utils.BasicGeometry

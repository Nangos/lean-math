import LeanMath.Utils.BasicGeometry.Common

namespace Utils.BasicGeometry

/-- Internal representation of a line, providing various parameterized construction methods. -/
inductive Line.internal (n : ℕ)
  | /-- A line determined by two distinct points. -/
    Point2 (p₁ p₂ : Point n) (valid : p₁ ≠ p₂)

/-- Evaluates the internal representation of a line into a standard set of points. -/
noncomputable def Line.internal.toPointSet {n : ℕ} : Line.internal n → Set (Point n)
  | Point2 p₁ p₂ _ => { p | ∃ (t : ℝ), p = AffineMap.lineMap p₁ p₂ t }

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
noncomputable def Line.toPointSet {n : ℕ} (l : Line n) : PointSet n :=
  Quotient.lift Line.internal.toPointSet (fun _ _ h => h) l

/-- Instantiates `Line n` as a `PointSet`, allowing its treating as a set of points. -/
instance {n : ℕ} : ToPointSet n (Line n) := ⟨Line.toPointSet⟩


/-- A line in 2-dimensional space (a.k.a. in a plane). -/
abbrev Line2D := Line 2

/-- Constructs a Line2D from a slope `k` and y-intercept `y₀` in coordinate system `Φ`:
`{ p | p.y = k * p.x + y₀ }`. -/
noncomputable def Line2D.fromSlopeY {Φ : CoordSys 2} {k y₀ : ℝ} (formula : PointViewSet Φ)
    (_h : formula = { p : PointView Φ | p.y = k * p.x + y₀ } := by rfl) : Line2D :=
  -- The line passes through points (0, y₀) and (1, k + y₀).
  Line.ofPoint2 (Φ.symm ![0, y₀]) (Φ.symm ![1, k + y₀]) (by
    intro h
    have h_coord := congrArg Φ h
    simp only [AffineEquiv.apply_symm_apply] at h_coord
    have h_zero : (0 : ℝ) = 1 := by
      calc (0 : ℝ) = (![0, y₀] : Fin 2 → ℝ) 0 := rfl
      _ = (![1, k + y₀] : Fin 2 → ℝ) 0 := congrFun h_coord 0
      _ = 1 := rfl
    norm_num at h_zero)

/-- Asserts the consistency of the `Line2D.fromSlopeY` construction. Namely, the resulting line
has the expected point set in the given coordinate system. -/
theorem Line2D.fromSlopeY_view_consistent {Φ : CoordSys 2} {k y₀ : ℝ} (formula : PointViewSet Φ)
    (_h : formula = { p : PointView Φ | p.y = k * p.x + y₀ } := by rfl) :
    (Line2D.fromSlopeY formula _h).toPointSet.view Φ = formula := by
  -- I do not understand this, but Gemini made it and it works. Happy "vibe proving" :)
  subst _h; ext p
  dsimp [PointViewSet, PointSet.view, Line2D.fromSlopeY, Line.ofPoint2, Line.toPointSet]
  constructor
  · rintro ⟨t, ht⟩
    have ht_coord : Φ ↑p = AffineMap.lineMap ![0, y₀] ![1, k + y₀] t := by
      have h1 : Φ.toAffineMap ↑p =
        Φ.toAffineMap (AffineMap.lineMap (Φ.symm ![0, y₀]) (Φ.symm ![1, k + y₀]) t) := by rw [ht]
      rw [AffineMap.apply_lineMap Φ.toAffineMap] at h1
      have eq0 : Φ (Φ.symm ![0, y₀]) = ![0, y₀] := AffineEquiv.apply_symm_apply Φ ![0, y₀]
      have eq1 : Φ (Φ.symm ![1, k + y₀]) = ![1, k + y₀] :=
        AffineEquiv.apply_symm_apply Φ ![1, k + y₀]
      change Φ ↑p = AffineMap.lineMap (Φ (Φ.symm ![0, y₀])) (Φ (Φ.symm ![1, k + y₀])) t at h1
      rw [eq0, eq1] at h1
      exact h1
    have hx : p.x = t := by
      calc p.x = (Φ ↑p) 0 := rfl
           _ = (AffineMap.lineMap ![0, y₀] ![1, k + y₀] t) 0 := congrFun ht_coord 0
           _ = t := by simp [AffineMap.lineMap]
    have hy : p.y = k * t + y₀ := by
      calc p.y = (Φ ↑p) 1 := rfl
           _ = (AffineMap.lineMap ![0, y₀] ![1, k + y₀] t) 1 := congrFun ht_coord 1
           _ = k * t + y₀ := by simp [AffineMap.lineMap]; ring
    rw [hx]; exact hy
  · intro hp; use p.x
    dsimp [PointView.y, PointView.x, PointView.coord] at hp
    apply EquivLike.injective Φ
    have h_target : Φ (AffineMap.lineMap (Φ.symm ![0, y₀]) (Φ.symm ![1, k + y₀]) p.x) =
      AffineMap.lineMap ![0, y₀] ![1, k + y₀] p.x := by
      have h1 : Φ.toAffineMap (AffineMap.lineMap (Φ.symm ![0, y₀]) (Φ.symm ![1, k + y₀]) p.x) =
        AffineMap.lineMap (Φ.toAffineMap (Φ.symm ![0, y₀]))
        (Φ.toAffineMap (Φ.symm ![1, k + y₀])) p.x :=
        AffineMap.apply_lineMap Φ.toAffineMap (Φ.symm ![0, y₀]) (Φ.symm ![1, k + y₀]) p.x
      have eq0 : Φ (Φ.symm ![0, y₀]) = ![0, y₀] := AffineEquiv.apply_symm_apply Φ ![0, y₀]
      have eq1 : Φ (Φ.symm ![1, k + y₀]) = ![1, k + y₀] :=
        AffineEquiv.apply_symm_apply Φ ![1, k + y₀]
      change Φ (AffineMap.lineMap (Φ.symm ![0, y₀]) (Φ.symm ![1, k + y₀]) p.x) =
        AffineMap.lineMap (Φ (Φ.symm ![0, y₀])) (Φ (Φ.symm ![1, k + y₀])) p.x at h1
      rw [eq0, eq1] at h1
      exact h1
    rw [h_target]
    ext i; fin_cases i
    · have h_0 : (AffineMap.lineMap ![0, y₀] ![1, k + y₀] p.x) 0 = p.x := by
        simp [AffineMap.lineMap]
      calc (Φ ↑p) 0 = p.x := rfl
           _ = (AffineMap.lineMap ![0, y₀] ![1, k + y₀] p.x) 0 := h_0.symm
    · have h_1 : (AffineMap.lineMap ![0, y₀] ![1, k + y₀] p.x) 1 = k * p.x + y₀ := by
        simp [AffineMap.lineMap]; ring
      calc (Φ ↑p) 1 = k * p.x + y₀ := hp
           _ = (AffineMap.lineMap ![0, y₀] ![1, k + y₀] p.x) 1 := h_1.symm

example {Φ : CoordSys 2} :
    (Line2D.fromSlopeY { p : PointView Φ | p.y = 2 * p.x - 3 }).toPointSet.view Φ
    = { p | p.y = 2 * p.x - 3 } := by
  simp [Line2D.fromSlopeY_view_consistent]

end Utils.BasicGeometry

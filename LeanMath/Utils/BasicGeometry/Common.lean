import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Utils.BasicGeometry

/-- A point in an n-dimensional Euclidean space. -/
abbrev Point (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- A vector in an n-dimensional Euclidean space. Semantically distinguished from a point. -/
abbrev Vec (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- A set of points in an n-dimensional Euclidean space. -/
abbrev PointSet (n : ℕ) := Set (Point n)

/-- A type class for types that can be interpreted as a set of points in an n-dimensional
Euclidean space representations (`Set (Point n)`). -/
class ToPointSet (n : ℕ) (S : Type*) where
  /-- Converts the object into a standard set of points. -/
  toPointSet : S → Set (Point n)

/-- Coordinate system, essentially an affine bijection between abstract points `Point n` and real
coordinate tuples `Fin n → ℝ`. -/
abbrev CoordSys (n : ℕ) := Point n ≃ᵃ[ℝ] (Fin n → ℝ)

/-- A point localized to a specific coordinate system `Φ`, holding the underlying
coordinate-free point data. -/
structure PointView {n : ℕ} (Φ : CoordSys n) where
  /-- The underlying coordinate-free point. -/
  point : Point n

/-- Allows `PointView Φ` to be seamlessly and transparently coerced into a standard `Point n`
for pure geometric computations. This coercion has no overhead at the data level. -/
instance {n : ℕ} {Φ : CoordSys n} : CoeOut (PointView Φ) (Point n) where
  coe p := p.point

/-- Gets the specific coordinate array of the point evaluate under the specific coordinate
system `Φ`. -/
noncomputable def PointView.coord {n : ℕ} {Φ : CoordSys n} (p : PointView Φ) : (Fin n → ℝ) :=
  Φ ↑p

/-- Gets the first coordinate (x) of the point under the current coordinate system. -/
noncomputable def PointView.x {n : ℕ} {Φ : CoordSys n} (p : PointView Φ) (h : 1 ≤ n := by omega)
    : ℝ :=
  p.coord ⟨0, by omega⟩

/-- Gets the second coordinate (y) of the point under the current coordinate system. -/
noncomputable def PointView.y {n : ℕ} {Φ : CoordSys n} (p : PointView Φ) (h : 2 ≤ n := by omega)
    : ℝ :=
  p.coord ⟨1, by omega⟩

/-- Gets the third coordinate (z) of the point under the current coordinate system. -/
noncomputable def PointView.z {n : ℕ} {Φ : CoordSys n} (p : PointView Φ) (h : 3 ≤ n := by omega)
    : ℝ :=
  p.coord ⟨2, by omega⟩

/-- A set of points localized to a specific coordinate system `Φ`. -/
abbrev PointViewSet {n : ℕ} (Φ : CoordSys n) := Set (PointView Φ)

/-- Converts a pure point set into a coordinate-dependent point view set. -/
def PointSet.view {n : ℕ} (S : PointSet n) (Φ : CoordSys n) : PointViewSet Φ :=
  { p : PointView Φ | ↑p ∈ S }

end Utils.BasicGeometry

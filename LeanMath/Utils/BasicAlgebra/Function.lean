import Mathlib.Tactic

/-! Some basic properties about general functions. -/
namespace Utils.BasicAlgebra

/-- A function is odd if `f(-x) = -f(x)` for all `x`. -/
abbrev isOdd {α β} [Neg α] [Neg β] (f : α → β) :=
  ∀ x, f (-x) = - f x

/-- A function is even if `f(-x) = f(x)` for all `x`. -/
abbrev isEven {α β} [Neg α] (f : α → β) :=
  ∀ x, f (-x) = f x

/-- A function has period `p` if `f(x + p) = f(x)` for all `x`. -/
abbrev hasPeriod {α β} [Add α] (f : α → β) (p : α) :=
  ∀ x, f (x + p) = f x

end Utils.BasicAlgebra

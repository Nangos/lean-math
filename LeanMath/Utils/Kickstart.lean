import Mathlib.Tactic

namespace Utils.Kickstart
set_option linter.style.multiGoal false

private def x : ℤ := 2
private def y : ℤ := 3

/-- Create a challange to find **one** solution to `P`, represented as a set. -/
abbrev find_one {α} (P : Set α) := Σ' e, e ∈ P
/-- Create a challange to find **all** solutions to `P`, represented as a set. -/
abbrev find_all {α} (P : Set α) := Σ' S, S = P

/-- Use the `start!` macro to kickstart the challenge solving process. -/
macro "start!" : tactic => `(tactic| (refine ⟨?ans, ?proof⟩; swap))
/-- Use the `answer! ...` macro to explicitly provide an answer once you're ready. -/
macro "answer!" t:term : tactic => `(tactic| (swap; exact $t))

-- Showcases:
private def easy : find_one { _? | _? = x + y } := by
  start!
  simp [x, y]
  answer! 5
  rfl

example : find_all { _? | _? = x + y } := by
  start!
  simp [x, y]
  answer! {5}
  rfl

/-- Use the `reuse! ... from ... as ...` macro to reuse a previously solved challenge. -/
macro "reuse!" val:term "from" t:term "as" h_name:ident : tactic =>
  `(tactic| (
    let _temp_sigma_ := $t
    have _temp_val_ : _temp_sigma_.1 = $val := by rfl
    rcases _temp_sigma_ with ⟨_temp_sigma_, $h_name⟩
    simp at _temp_val_
    subst _temp_val_
  ))

example : 5 = x + y := by
  reuse! 5 from easy as h
  simp at h
  exact h

/-- Create a challenge to choose **one** option that satisfies `P`, represented as a set. -/
abbrev choose_one {α β} (P : Set α) (choices : β → α) := Σ' c, choices c ∈ P
/-- Create a challenge to choose **all** options that satisfy `P`, represented as a set. -/
abbrev choose_all {α β} (P : Set α) (choices : β → α) := Σ' S, S = {c | choices c ∈ P}
/-- Create a challenge to choose the option that *minimizes* the target function `F`. -/
abbrev choose_least {α γ β} [LinearOrder γ] (F : α → γ) (choices : β → α) :=
  Σ' c, ∀ c', F (choices c) ≤ F (choices c')

/-- The default 4-choice setting for GaoKao math problems. Override this if needed. -/
inductive Choice | A | B | C | D

-- Question: choose the correct value of `x + y`.
example : choose_one { _? | _? = x + y } (match · with
  | Choice.A => 1
  | Choice.B => 3
  | Choice.C => 5
  | Choice.D => 7) := by
  start!
  simp [x, y]
  answer! Choice.C
  rfl

-- Question: choose all following propositions that are `true`.
example : choose_all { _? | _? = True } (match · with
  | Choice.A => x > y
  | Choice.B => x < y
  | Choice.C => x ≥ y
  | Choice.D => x ≤ y) := by
  start!
  simp [x, y]
  answer! {Choice.B, Choice.D}
  grind

/-- Given a choice list, push function `F` into each of its match arms. -/
theorem Choice.push {α β} (F : α → β) (c : Choice) (vA vB vC vD : α) :
    F (match c with | .A => vA | .B => vB | .C => vC | .D => vD)
    = (match c with | .A => F vA | .B => F vB | .C => F vC | .D => F vD) := by
  grind

-- Question: choose the option that is closest to 42.
example : choose_least (|· - 42|) (match · with
  | Choice.A => x + y
  | Choice.B => x - y
  | Choice.C => x * y
  | Choice.D => x / y) := by
  start!
  simp [x, y]
  simp [Choice.push (|· - (42 : ℤ)|)]
  answer! Choice.C
  grind

end Utils.Kickstart

import Mathlib.Tactic

namespace Utils.Kickstart

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.multiGoal false

private def x : ℤ := 2
private def y : ℤ := 3

/-- Create a challange to find **one** solution to `P`, represented as a set. -/
abbrev find_one {α} (P : Set α) := Σ' e, e ∈ P
/-- Create a challange to find **all** solutions to `P`, represented as a set. -/
abbrev find_all {α} (P : Set α) := Σ' S, S = P

/-- Use the `answer! ...` macro to explicitly provide an answer once you're ready. -/
macro "answer!" t:term : tactic => `(tactic| refine ⟨$t, ?proof⟩)

/-- Use the `answer_later!` macro to "pretend" there is an answer, which can enable further
  simplifications. This macro should NOT be used too early. -/
macro "answer_later!" : tactic => `(tactic| (refine ⟨?ans, ?proof⟩; swap))

/-- Used the `answer_now! ...` macro to explicitly provide an answer.
  Should ONLY be used after `answer_later!`. -/
macro "answer_now!" t:term : tactic => `(tactic| (swap; exact $t))

-- Showcases:
private def easy : find_one { _? | _? = x + y } := by
  simp [x, y]
  answer! 5
  rfl

example : find_all { _? | _? = x + y } := by
  answer_later!
  simp [x, y]
  answer_now! {5}
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
  simp [x, y]
  answer! Choice.C
  rfl

-- Question: choose all following propositions that are `true`.
example : choose_all { _? | _? = True } (match · with
  | Choice.A => x > y
  | Choice.B => x < y
  | Choice.C => x ≥ y
  | Choice.D => x ≤ y) := by
  simp [x, y]
  answer! {Choice.B, Choice.D}
  grind

/-- Given a choice list, push function `F` into each of its match arms. -/
theorem Choice.push {α β} (F : α → β) (c : Choice) (vA vB vC vD : α) :
    F (match c with | .A => vA | .B => vB | .C => vC | .D => vD)
    = (match c with | .A => F vA | .B => F vB | .C => F vC | .D => F vD) := by
  cases c <;> rfl

-- Question: choose the option that is closest to 42.
example : choose_least (|· - 42|) (match · with
  | Choice.A => x + y
  | Choice.B => x - y
  | Choice.C => x * y
  | Choice.D => x / y) := by
  simp [x, y]
  answer_later!
  simp [Choice.push (|· - (42 : ℤ)|)]
  answer_now! Choice.C
  grind

end Utils.Kickstart

import Mathlib.Tactic

namespace Utils.Kickstart
set_option linter.style.multiGoal false

-- Define some variables and hypotheses for the later use in the examples.
variable (x : ℕ) (hx : x = 2)
variable (y : ℕ) (hy : y = 3)

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
  simp [*]
  answer! 5
  rfl

example : find_all { _? | _? = x + y } := by
  start!
  simp [*]
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
  reuse! 5 from easy x hx y hy as h
  clear hx hy
  simp at h; trivial

/-- Create a challenge to choose **one** option that satisfies `P`, represented as a set. -/
abbrev choose_one {α β} (P : Set α) (choices : β → α) := Σ' c, choices c ∈ P
/-- Create a challenge to choose **all** options that satisfy `P`, represented as a set. -/
abbrev choose_all {α β} (P : Set α) (choices : β → α) := Σ' S, S = {c | choices c ∈ P}

private inductive Choice | A | B | C | D

example : choose_one { _? | _? = x + y } (match · with
  | Choice.A => 1
  | Choice.B => 3
  | Choice.C => 5
  | Choice.D => 7) := by
  start!
  simp [*]
  answer! Choice.C
  rfl

example : choose_all { _? | _? = True } (match · with
  | Choice.A => x > y
  | Choice.B => x < y
  | Choice.C => x ≥ y
  | Choice.D => x ≤ y) := by
  start!
  simp [*]
  answer! {Choice.B, Choice.D}
  grind

end Utils.Kickstart

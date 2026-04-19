# LeanMath: Constructive Math Problem Solving

This project explores a **constructive** approach to math formalization in **Lean 4**, focusing on deriving answers *during* the proof process rather than stating them upfront.

## Motivation

Standard Lean formalization usually requires providing the answer upfront in the theorem statement. However, in real-world problem-solving, we often don't know the answer until we've simplified the conditions. This project aims to bridge that gap: *Can we use Lean to calculate the result while proving it?*

## Core Mechanism

Instead of a standard theorem, we represent problems as **Sigma types**—mathematical "containers" that require you to provide both a concrete value and a proof that it satisfies the given conditions.

We utilize metavariables and macros to defer the solution:
1. **`answer_later!`**: Splits the goal into a result metavariable and a proof requirement.
2. **Flexible Timing**: Use tactics (`simp`, `linarith`, `grind`) to reduce the problem. You can provide the answer at the beginning, middle, or the very end of the script.
3. **`answer_now! <val>`**: Fills the metavariable with your calculated result once the proof is simplified.

**Note:** I am a Lean beginner, and this is a "learn-by-doing" project. Feedback and suggestions are highly welcome!

## Sister Project
[LeanCode: Formally Verified LeetCode](https://github.com/Nangos/lean-code/)

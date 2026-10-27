import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.FiniteInjectivePerturbation
open Metric Set


/--
[complex_ball_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/FiniteInjectivePerturbation.lean)
-/
@[path]
private lemma complex_ball_infinite_eq
  {z : Complex}
  {r : Real}
-- given
  (hr : 0 < r) :
-- imply
  (ball z r).Infinite := by
-- proof
  apply complex_ball_infinite z hr

/--
[exists_injective_perturbation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/FiniteInjectivePerturbation.lean)
-/
@[path]
private lemma exists_injective_perturbation_eq
  {α : Type}
  [Fintype α]
  {f : α → Complex}
  {r : Real}
-- given
  (hr : 0 < r) :
-- imply
  ∃ g : α → Complex, Function.Injective g ∧ ∀ a, dist (g a) (f a) < r := by
-- proof
  apply exists_injective_perturbation f hr


-- created on 2026-10-23

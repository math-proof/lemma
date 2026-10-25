import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FiniteSurjectionOneExcess
open Finset StatMech StatMech.FrontierD


/--
[finiteSurjection_fiber_eq_pair_of_card_eq_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteSurjectionOneExcess.lean)
-/
@[path]
private lemma finiteSurjection_fiber_eq_pair_of_card_eq_add_one_eq
  [Fintype A]
  [Fintype B]
  [DecidableEq A]
  [DecidableEq B]
  {f : A → B}
  {a b : A}
-- given
  (hf : Function.Surjective f)
  (hcard : Fintype.card A = Fintype.card B + 1)
  (hab : a ≠ b)
  (hfab : f a = f b) :
-- imply
  ∀ x : A, f x = f a → x = a ∨ x = b := by
-- proof
  apply StatMech.FrontierD.finiteSurjection_fiber_eq_pair_of_card_eq_add_one f hf hcard hab hfab

/--
[finiteSurjection_fiber_eq_singleton_away_of_card_eq_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteSurjectionOneExcess.lean)
-/
@[path]
private lemma finiteSurjection_fiber_eq_singleton_away_of_card_eq_add_one_eq
  [Fintype A]
  [Fintype B]
  [DecidableEq A]
  [DecidableEq B]
  {f : A → B}
  {a b : A}
  {x : A}
-- given
  (hf : Function.Surjective f)
  (hcard : Fintype.card A = Fintype.card B + 1)
  (hab : a ≠ b)
  (hfab : f a = f b)
  (hxaway : f x ≠ f a) :
-- imply
  ∀ y : A, f y = f x → y = x := by
-- proof
  apply StatMech.FrontierD.finiteSurjection_fiber_eq_singleton_away_of_card_eq_add_one f hf hcard hab hfab hxaway


-- created on 2026-10-23

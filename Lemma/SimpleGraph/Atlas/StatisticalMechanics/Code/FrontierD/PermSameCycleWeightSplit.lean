import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.PermSameCycleWeightSplit
open Equiv Finset StatMech StatMech.FrontierD


/--
[permCycleClassWeightSum_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/PermSameCycleWeightSplit.lean)
-/
@[path]
private lemma permCycleClassWeightSum_split_eq
  [Fintype D]
  [DecidableEq D]
  [AddCommGroup A]
  {σ : Perm D}
  {a b : D}
  {f g : D → A}
-- given
  (habne : a ≠ b)
  (hab : σ.SameCycle a b)
  (hcount : permCycleCount (σ * Equiv.swap a b) = permCycleCount σ + 1)
  (haway : ∀ x, x ≠ a → x ≠ b → f x = g x)
  (hpair : f a + f b = g a + g b) :
-- imply
  permCycleClassWeightSum σ a f = permCycleClassWeightSum (σ * Equiv.swap a b) a g + permCycleClassWeightSum (σ * Equiv.swap a b) b g := by
-- proof
  apply StatMech.FrontierD.permCycleClassWeightSum_split σ a b habne hab hcount f g haway hpair

/--
[permCycleClassWeightSum_eq_of_not_sameCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/PermSameCycleWeightSplit.lean)
-/
@[path]
private lemma permCycleClassWeightSum_eq_of_not_sameCycle_eq
  [Fintype D]
  [DecidableEq D]
  [AddCommGroup A]
  {σ : Perm D}
  {a b x : D}
  {f g : D → A}
-- given
  (habne : a ≠ b)
  (hab : σ.SameCycle a b)
  (hcount : permCycleCount (σ * Equiv.swap a b) = permCycleCount σ + 1)
  (hx : ¬ σ.SameCycle a x)
  (haway : ∀ y, y ≠ a → y ≠ b → f y = g y) :
-- imply
  permCycleClassWeightSum σ x f = permCycleClassWeightSum (σ * Equiv.swap a b) x g := by
-- proof
  apply StatMech.FrontierD.permCycleClassWeightSum_eq_of_not_sameCycle σ a b x habne hab hcount hx f g haway


-- created on 2026-10-23

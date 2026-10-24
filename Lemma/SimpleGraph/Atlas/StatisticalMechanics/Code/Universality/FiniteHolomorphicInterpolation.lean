import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.FiniteHolomorphicInterpolation
open Finset


/--
[finiteLagrangeBasis_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/FiniteHolomorphicInterpolation.lean)
-/
@[path]
private lemma finiteLagrangeBasis_self_eq
  [Fintype α]
  [DecidableEq α]
  {position : α → Complex}
  {a : α}
-- given
  (hposition : Function.Injective position) :
-- imply
  finiteLagrangeBasis position a (position a) = 1 := by
-- proof
  apply finiteLagrangeBasis_self position hposition a

/--
[finiteLagrangeBasis_apply_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/FiniteHolomorphicInterpolation.lean)
-/
@[path]
private lemma finiteLagrangeBasis_apply_eq_zero_eq
  [Fintype α]
  [DecidableEq α]
  {position : α → Complex}
  {a b : α}
-- given
  (hab : a ≠ b) :
-- imply
  finiteLagrangeBasis position b (position a) = 0 := by
-- proof
  apply finiteLagrangeBasis_apply_eq_zero position a b hab

/--
[finiteLagrangeInterpolant_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/FiniteHolomorphicInterpolation.lean)
-/
@[path]
private lemma finiteLagrangeInterpolant_apply_eq
  [Fintype α]
  [DecidableEq α]
  {position value : α → Complex}
  {a : α}
-- given
  (hposition : Function.Injective position) :
-- imply
  finiteLagrangeInterpolant position value (position a) = value a := by
-- proof
  apply finiteLagrangeInterpolant_apply position value hposition a

/--
[differentiable_finiteLagrangeBasis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/FiniteHolomorphicInterpolation.lean)
-/
@[path]
private lemma differentiable_finiteLagrangeBasis_eq
  [Fintype α]
  [DecidableEq α]
  {position : α → Complex}
  {a : α} :
-- imply
  Differentiable Complex (finiteLagrangeBasis position a) := by
-- proof
  apply differentiable_finiteLagrangeBasis position a

/--
[differentiable_finiteLagrangeInterpolant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/FiniteHolomorphicInterpolation.lean)
-/
@[path]
private lemma differentiable_finiteLagrangeInterpolant_eq
  [Fintype α]
  [DecidableEq α]
  {position value : α → Complex} :
-- imply
  Differentiable Complex (finiteLagrangeInterpolant position value) := by
-- proof
  apply differentiable_finiteLagrangeInterpolant position value


-- created on 2026-10-23

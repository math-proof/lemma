import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopAnchoredCut
open Finset StatMech StatMech.Onsager


/--
[optionInteriorCutSum_eq_anchored](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopAnchoredCut.lean)
-/
@[path]
private lemma optionInteriorCutSum_eq_anchored_eq
  [Fintype I]
  [DecidableEq I]
  [Fintype P]
  [DecidableEq P]
  {ends : P → Option I × Option I}
  {observable : Finset P → Real} :
-- imply
  (∑ tau : I → Bool, observable (multibondCut ends (ons_optionAnchoredEquiv tau).1)) = ∑ config : AnchoredConfig (Option I) none, observable (multibondCut ends config.1) := by
-- proof
  apply StatMech.Onsager.optionInteriorCutSum_eq_anchored ends observable

/--
[multibondCutSum_eq_two_mul_anchored](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopAnchoredCut.lean)
-/
@[path]
private lemma multibondCutSum_eq_two_mul_anchored_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype P]
  [DecidableEq P]
  {ends : P → V × V}
  {root : V}
  {observable : Finset P → Real} :
-- imply
  (∑ config : V → Bool, observable (multibondCut ends config)) = 2 * ∑ config : AnchoredConfig V root, observable (multibondCut ends config.1) := by
-- proof
  apply StatMech.Onsager.multibondCutSum_eq_two_mul_anchored ends root observable


-- created on 2026-10-23

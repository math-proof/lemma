import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAcyclicElimination.Part3
open StatMech StatMech.FrontierA


/--
[kw_fourPort_even_iff_unique_trivalent_completion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAcyclicElimination.lean)
-/
@[path]
private lemma kw_fourPort_even_iff_unique_trivalent_completion_eq
  {b0 b1 b2 b3 : Fin 2} :
-- imply
  b0 + b1 + b2 + b3 = 0 ↔ ∃! y : Fin 3 -> Fin 2, StatMech.Onsager.ons_decChainEven b0 b1 b2 b3 y := by
-- proof
  apply StatMech.FrontierA.kw_fourPort_even_iff_unique_trivalent_completion b0 b1 b2 b3

/--
[kwNilpotentResolvent_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAcyclicElimination.lean)
-/
@[path]
private lemma kwNilpotentResolvent_mul_eq
  [Fintype Internal]
  [DecidableEq Internal]
  {internal : Matrix Internal Internal ℂ}
  {nilpotenceIndex : ℕ}
-- given
  (hpow : internal ^ nilpotenceIndex = 0) :
-- imply
  kwNilpotentResolvent internal nilpotenceIndex * (1 - internal) = 1 := by
-- proof
  apply StatMech.FrontierA.kwNilpotentResolvent_mul internal nilpotenceIndex hpow

/--
[kw_mul_nilpotentResolvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAcyclicElimination.lean)
-/
@[path]
private lemma kw_mul_nilpotentResolvent_eq
  [Fintype Internal]
  [DecidableEq Internal]
  {internal : Matrix Internal Internal ℂ}
  {nilpotenceIndex : ℕ}
-- given
  (hpow : internal ^ nilpotenceIndex = 0) :
-- imply
  (1 - internal) * kwNilpotentResolvent internal nilpotenceIndex = 1 := by
-- proof
  apply StatMech.FrontierA.kw_mul_nilpotentResolvent internal nilpotenceIndex hpow

/--
[kw_one_sub_internalGadget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAcyclicElimination.lean)
-/
@[path]
private lemma kw_one_sub_internalGadget_eq
  [Fintype External]
  [DecidableEq External]
  [Fintype Internal]
  [DecidableEq Internal]
  {external : Matrix External External ℂ}
  {enter : Matrix External Internal ℂ}
  {exit : Matrix Internal External ℂ}
  {internal : Matrix Internal Internal ℂ} :
-- imply
  1 - kwInternalGadgetTransition external enter exit internal = Matrix.fromBlocks (1 - external) (-enter) (-exit) (1 - internal) := by
-- proof
  apply StatMech.FrontierA.kw_one_sub_internalGadget external enter exit internal

/--
[kw_det_eliminateAcyclicInternal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAcyclicElimination.lean)
-/
@[path]
private lemma kw_det_eliminateAcyclicInternal_eq
  [Fintype External]
  [DecidableEq External]
  [Fintype Internal]
  [DecidableEq Internal]
  {external : Matrix External External ℂ}
  {enter : Matrix External Internal ℂ}
  {exit : Matrix Internal External ℂ}
  {internal : Matrix Internal Internal ℂ}
  {nilpotenceIndex : ℕ}
-- given
  (hpow : internal ^ nilpotenceIndex = 0) :
-- imply
  (1 - kwInternalGadgetTransition external enter exit internal).det = (1 - kwEliminateAcyclicInternal external enter exit internal nilpotenceIndex).det := by
-- proof
  apply StatMech.FrontierA.kw_det_eliminateAcyclicInternal external enter exit internal nilpotenceIndex hpow


-- created on 2026-10-23

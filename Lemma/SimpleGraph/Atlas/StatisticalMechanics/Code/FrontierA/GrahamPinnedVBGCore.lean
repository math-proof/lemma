import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamPinnedVBGCore
open Finset Classical StatMech StatMech.FrontierA


/--
[grahamZeroProb_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedVBGCore.lean)
-/
@[path]
private lemma grahamZeroProb_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
-- given
  (J : Sym2 V -> Real) :
-- imply
  (0 : ConfigSpace V -> Real) <= grahamZeroProb E J := by
-- proof
  apply StatMech.FrontierA.grahamZeroProb_nonneg E J

/--
[grahamZeroProb_sum_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedVBGCore.lean)
-/
@[path]
private lemma grahamZeroProb_sum_eq_one_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
-- given
  (J : Sym2 V -> Real) :
-- imply
  ∑ s, grahamZeroProb E J s = 1 := by
-- proof
  apply StatMech.FrontierA.grahamZeroProb_sum_eq_one E J

/--
[vbg_exp_grahamZeroProb_eq_expJ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedVBGCore.lean)
-/
@[path]
private lemma vbg_exp_grahamZeroProb_eq_expJ_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
-- given
  (J : Sym2 V -> Real)
  (f : ConfigSpace V -> Real) :
-- imply
  vbg_exp (grahamZeroProb E J) f = expJ E J (fun _ => 0) f := by
-- proof
  apply StatMech.FrontierA.vbg_exp_grahamZeroProb_eq_expJ E J f

/--
[graham_wJ_zero_logSupermodular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedVBGCore.lean)
-/
@[path]
private lemma graham_wJ_zero_logSupermodular_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
-- given
  (J : Sym2 V -> Real)
  (hJ : ∀ e ∈ E, 0 <= J e) :
-- imply
  StatMech.FKGLatticeCondition (wJ E J (fun _ => 0)) := by
-- proof
  apply StatMech.FrontierA.graham_wJ_zero_logSupermodular E J hJ

/--
[grahamZeroProb_FKG](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedVBGCore.lean)
-/
@[path]
private lemma grahamZeroProb_FKG_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
-- given
  (J : Sym2 V -> Real)
  (hJ : ∀ e ∈ E, 0 <= J e) :
-- imply
  StatMech.FKGLatticeCondition (grahamZeroProb E J) := by
-- proof
  apply StatMech.FrontierA.grahamZeroProb_FKG E J hJ

/--
[expJ_zero_spin_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedVBGCore.lean)
-/
@[path]
private lemma expJ_zero_spin_eq_zero_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {x : V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  expJ E J (fun _ => 0) (fun s => spin s x) = 0 := by
-- proof
  apply StatMech.FrontierA.expJ_zero_spin_eq_zero E J x

/--
[expJ_zero_spinProd_odd_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedVBGCore.lean)
-/
@[path]
private lemma expJ_zero_spinProd_odd_eq_zero_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {A : Finset V}
-- given
  (J : Sym2 V -> Real)
  (hA : Odd A.card) :
-- imply
  expJ E J (fun _ => 0) (spinProd A) = 0 := by
-- proof
  apply StatMech.FrontierA.expJ_zero_spinProd_odd_eq_zero E J A hA


-- created on 2026-10-23

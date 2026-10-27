import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamAgreementVBG
open Finset SimpleGraph Classical StatMech StatMech.FrontierA


/--
[grahamReplicaAgree_mate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamAgreementVBG.lean)
-/
@[path]
private lemma grahamReplicaAgree_mate_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q a : ConfigSpace V}
  {k : V} :
-- imply
  grahamReplicaAgree a (ghsLMate q a) k = vbg_coordUp k q := by
-- proof
  apply StatMech.FrontierA.grahamReplicaAgree_mate G q a k

/--
[grahamReplicaAgree_eq_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamAgreementVBG.lean)
-/
@[path]
private lemma grahamReplicaAgree_eq_half_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {a b : ConfigSpace V}
  {k : V} :
-- imply
  grahamReplicaAgree a b k = (1 + spin a k * spin b k) / 2 := by
-- proof
  apply StatMech.FrontierA.grahamReplicaAgree_eq_half G a b k

/--
[grahamReplicaAgree_mul_tvar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamAgreementVBG.lean)
-/
@[path]
private lemma grahamReplicaAgree_mul_tvar_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {a b : ConfigSpace V}
  {k : V} :
-- imply
  grahamReplicaAgree a b k * tvar a b k = tvar a b k := by
-- proof
  apply StatMech.FrontierA.grahamReplicaAgree_mul_tvar G a b k

/--
[ghsLFibreExpectation_mul_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamAgreementVBG.lean)
-/
@[path]
private lemma ghsLFibreExpectation_mul_agree_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {k : V}
  {q : ConfigSpace V}
-- given
  (beta h : Real)
  (F : ConfigSpace V -> ConfigSpace V -> Real) :
-- imply
  ghsLFibreExpectation G beta h (fun a b => F a b * grahamReplicaAgree a b k) q = ghsLFibreExpectation G beta h F q * vbg_coordUp k q := by
-- proof
  apply StatMech.FrontierA.ghsLFibreExpectation_mul_agree G beta h F k q

/--
[ghsLFibreExpectation_eq_of_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamAgreementVBG.lean)
-/
@[path]
private lemma ghsLFibreExpectation_eq_of_fixed_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ConfigSpace V}
  {r : Real}
-- given
  (beta h : Real)
  (F : ConfigSpace V -> ConfigSpace V -> Real)
  (hF : forall a, F a (ghsLMate q a) = r) :
-- imply
  ghsLFibreExpectation G beta h F q = r := by
-- proof
  apply StatMech.FrontierA.ghsLFibreExpectation_eq_of_fixed G beta h F q r hF

/--
[ghsLFibreUU_self_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamAgreementVBG.lean)
-/
@[path]
private lemma ghsLFibreUU_self_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i : V}
  {q : ConfigSpace V}
-- given
  (beta h : Real) :
-- imply
  ghsLFibreUU G beta h i i q = 1 - vbg_coordUp i q := by
-- proof
  apply StatMech.FrontierA.ghsLFibreUU_self_eq G beta h i q

/--
[vbg_coordUp_monotone_local](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamAgreementVBG.lean)
-/
@[path]
private lemma vbg_coordUp_monotone_local_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i : V} :
-- imply
  Monotone (vbg_coordUp i : ConfigSpace V -> Real) := by
-- proof
  apply StatMech.FrontierA.vbg_coordUp_monotone_local G i

/--
[grahamAgreement_exp_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamAgreementVBG.lean)
-/
@[path]
private lemma grahamAgreement_exp_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {k : V}
-- given
  (beta h : Real) :
-- imply
  vbg_exp (ghsLAgreementProb G beta h) (vbg_coordUp k) = (1 + onePt G beta h k ^ 2) / 2 := by
-- proof
  apply StatMech.FrontierA.grahamAgreement_exp_eq G beta h k

/--
[grahamAgreement_exp_mul_fibreT](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamAgreementVBG.lean)
-/
@[path]
private lemma grahamAgreement_exp_mul_fibreT_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {k : V}
-- given
  (beta h : Real) :
-- imply
  vbg_exp (ghsLAgreementProb G beta h) (fun q => vbg_coordUp k q * ghsLFibreT G beta h k q) = onePt G beta h k := by
-- proof
  apply StatMech.FrontierA.grahamAgreement_exp_mul_fibreT G beta h k

/--
[grahamAgreement_exp_fibreT](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamAgreementVBG.lean)
-/
@[path]
private lemma grahamAgreement_exp_fibreT_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {k : V}
-- given
  (beta h : Real) :
-- imply
  vbg_exp (ghsLAgreementProb G beta h) (ghsLFibreT G beta h k) = onePt G beta h k := by
-- proof
  apply StatMech.FrontierA.grahamAgreement_exp_fibreT G beta h k

/--
[grahamAgreement_exp_fibreUU](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamAgreementVBG.lean)
-/
@[path]
private lemma grahamAgreement_exp_fibreUU_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j : V}
-- given
  (beta h : Real) :
-- imply
  vbg_exp (ghsLAgreementProb G beta h) (ghsLFibreUU G beta h i j) = cov2 G beta h i j / 2 := by
-- proof
  apply StatMech.FrontierA.grahamAgreement_exp_fibreUU G beta h i j

/--
[grahamAgreement_exp_fibreUU_mul_fibreT](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamAgreementVBG.lean)
-/
@[path]
private lemma grahamAgreement_exp_fibreUU_mul_fibreT_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k : V}
-- given
  (beta h : Real) :
-- imply
  vbg_exp (ghsLAgreementProb G beta h) (fun q => ghsLFibreUU G beta h i j q * ghsLFibreT G beta h k q) = isingExp2 G beta h (fun a b => uvar a b i * uvar a b j * tvar a b k) := by
-- proof
  apply StatMech.FrontierA.grahamAgreement_exp_fibreUU_mul_fibreT G beta h i j k

/--
[grahamAgreement_cov_fibreUU_fibreT](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamAgreementVBG.lean)
-/
@[path]
private lemma grahamAgreement_cov_fibreUU_fibreT_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k : V}
-- given
  (beta h : Real) :
-- imply
  vbg_cov (ghsLAgreementProb G beta h) (ghsLFibreUU G beta h i j) (ghsLFibreT G beta h k) = eg_ursell3 G beta h i j k / 4 := by
-- proof
  apply StatMech.FrontierA.grahamAgreement_cov_fibreUU_fibreT G beta h i j k

/--
[grahamAgreement_exp_fibreUU_mul_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamAgreementVBG.lean)
-/
@[path]
private lemma grahamAgreement_exp_fibreUU_mul_agree_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k : V}
-- given
  (beta h : Real) :
-- imply
  vbg_exp (ghsLAgreementProb G beta h) (fun q => ghsLFibreUU G beta h i j q * vbg_coordUp k q) = isingExp2 G beta h (fun a b => (uvar a b i * uvar a b j) * grahamReplicaAgree a b k) := by
-- proof
  apply StatMech.FrontierA.grahamAgreement_exp_fibreUU_mul_agree G beta h i j k

/--
[grahamUUAgree_expansion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamAgreementVBG.lean)
-/
@[path]
private lemma grahamUUAgree_expansion_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k : V}
-- given
  (beta h : Real) :
-- imply
  isingExp2 G beta h (fun a b => (uvar a b i * uvar a b j) * grahamReplicaAgree a b k) = (cov2 G beta h i j + onePt G beta h k * eg_ursell3 G beta h i j k - cov2 G beta h i k * cov2 G beta h j k + cov2 G beta h i j * onePt G beta h k ^ 2) / 4 := by
-- proof
  apply StatMech.FrontierA.grahamUUAgree_expansion G beta h i j k

/--
[grahamAgreement_cov_fibreUU_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamAgreementVBG.lean)
-/
@[path]
private lemma grahamAgreement_cov_fibreUU_agree_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k : V}
-- given
  (beta h : Real) :
-- imply
  vbg_cov (ghsLAgreementProb G beta h) (ghsLFibreUU G beta h i j) (vbg_coordUp k) = (onePt G beta h k * eg_ursell3 G beta h i j k - cov2 G beta h i k * cov2 G beta h j k) / 4 := by
-- proof
  apply StatMech.FrontierA.grahamAgreement_cov_fibreUU_agree G beta h i j k

/--
[grahamAgreement_cov_agree_fibreT](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamAgreementVBG.lean)
-/
@[path]
private lemma grahamAgreement_cov_agree_fibreT_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {k : V}
-- given
  (beta h : Real) :
-- imply
  vbg_cov (ghsLAgreementProb G beta h) (vbg_coordUp k) (ghsLFibreT G beta h k) = (1 - onePt G beta h k ^ 2) * onePt G beta h k / 2 := by
-- proof
  apply StatMech.FrontierA.grahamAgreement_cov_agree_fibreT G beta h k

/--
[grahamAgreement_var_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamAgreementVBG.lean)
-/
@[path]
private lemma grahamAgreement_var_agree_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {k : V}
-- given
  (beta h : Real) :
-- imply
  vbg_var (ghsLAgreementProb G beta h) (vbg_coordUp k) = (1 - onePt G beta h k ^ 4) / 4 := by
-- proof
  apply StatMech.FrontierA.grahamAgreement_var_agree G beta h k

/--
[grahamAgreement_coord_pos_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamAgreementVBG.lean)
-/
@[path]
private lemma grahamAgreement_coord_pos_lt_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {k : V}
-- given
  (beta h : Real) :
-- imply
  0 < vbg_exp (ghsLAgreementProb G beta h) (vbg_coordUp k) /\ vbg_exp (ghsLAgreementProb G beta h) (vbg_coordUp k) < 1 := by
-- proof
  apply StatMech.FrontierA.grahamAgreement_coord_pos_lt_one G beta h k

/--
[grahamImprovedGHS_agreement_strong](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamAgreementVBG.lean)
-/
@[path]
private lemma grahamImprovedGHS_agreement_strong_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k : V}
-- given
  (beta h : Real)
  (hbeta : 0 <= beta)
  (hh : 0 <= h) :
-- imply
  (1 - onePt G beta h k ^ 2) * (-eg_ursell3 G beta h i j k) >= 2 * onePt G beta h k * cov2 G beta h i k * cov2 G beta h j k := by
-- proof
  apply StatMech.FrontierA.grahamImprovedGHS_agreement_strong G beta h hbeta hh i j k

/--
[grahamImprovedGHS_agreement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamAgreementVBG.lean)
-/
@[path]
private lemma grahamImprovedGHS_agreement_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k : V}
-- given
  (beta h : Real)
  (hbeta : 0 <= beta)
  (hh : 0 <= h) :
-- imply
  eg_ursell3 G beta h i j k <= -2 * cov2 G beta h i k * cov2 G beta h j k * onePt G beta h k := by
-- proof
  apply StatMech.FrontierA.grahamImprovedGHS_agreement G beta h hbeta hh i j k

/--
[grahamImprovedGHS_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamAgreementVBG.lean)
-/
@[path]
private lemma grahamImprovedGHS_all_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k : V}
-- given
  (beta h : Real)
  (hbeta : 0 <= beta)
  (hh : 0 <= h) :
-- imply
  eg_ursell3 G beta h i j k <= grahamImprovedGHSRHS G beta h i j k := by
-- proof
  apply StatMech.FrontierA.grahamImprovedGHS_all G beta h hbeta hh i j k

/--
[grahamGhostCorrectedBound_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamAgreementVBG.lean)
-/
@[path]
private lemma grahamGhostCorrectedBound_all_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k : V}
-- given
  (beta h : Real)
  (hbeta : 0 <= beta)
  (hh : 0 <= h) :
-- imply
  gc_lebowitzU4 G beta h i j k <= grahamGhostCorrectedRHS G beta h i j k := by
-- proof
  apply StatMech.FrontierA.grahamGhostCorrectedBound_all G beta h hbeta hh i j k


-- created on 2026-10-23

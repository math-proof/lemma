import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamAgreementVBGInhomogeneous
open Finset SimpleGraph Classical StatMech StatMech.FrontierA


/--
[ghsiFibreExpectation_mul_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamAgreementVBGInhomogeneous.lean)
-/
@[path]
private lemma ghsiFibreExpectation_mul_agree_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {k : V}
  {q : ConfigSpace V}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real)
  (F : ConfigSpace V -> ConfigSpace V -> Real) :
-- imply
  ghsiFibreExpectation G K hf (fun a b => F a b * grahamReplicaAgree a b k) q = ghsiFibreExpectation G K hf F q * vbg_coordUp k q := by
-- proof
  apply StatMech.FrontierA.ghsiFibreExpectation_mul_agree G K hf F k q

/--
[ghsiFibreExpectation_eq_of_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamAgreementVBGInhomogeneous.lean)
-/
@[path]
private lemma ghsiFibreExpectation_eq_of_fixed_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ConfigSpace V}
  {r : Real}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real)
  (F : ConfigSpace V -> ConfigSpace V -> Real)
  (hF : forall a, F a (ghsLMate q a) = r) :
-- imply
  ghsiFibreExpectation G K hf F q = r := by
-- proof
  apply StatMech.FrontierA.ghsiFibreExpectation_eq_of_fixed G K hf F q r hF

/--
[ghsiFibreUU_self_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamAgreementVBGInhomogeneous.lean)
-/
@[path]
private lemma ghsiFibreUU_self_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i : V}
  {q : ConfigSpace V}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  ghsiFibreUU G K hf i i q = 1 - vbg_coordUp i q := by
-- proof
  apply StatMech.FrontierA.ghsiFibreUU_self_eq G K hf i q

/--
[grahamInhomOne_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamAgreementVBGInhomogeneous.lean)
-/
@[path]
private lemma grahamInhomOne_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x : V}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real)
  (hK : forall e, 0 <= K e)
  (hhf : forall x, 0 <= hf x) :
-- imply
  0 <= grahamInhomOne G K hf x := by
-- proof
  apply StatMech.FrontierA.grahamInhomOne_nonneg G K hf hK hhf x

/--
[grahamInhomOne_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamAgreementVBGInhomogeneous.lean)
-/
@[path]
private lemma grahamInhomOne_le_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x : V}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  grahamInhomOne G K hf x <= 1 := by
-- proof
  apply StatMech.FrontierA.grahamInhomOne_le_one G K hf x

/--
[grahamInhomCov_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamAgreementVBGInhomogeneous.lean)
-/
@[path]
private lemma grahamInhomCov_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j : V}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real)
  (hK : forall e, 0 <= K e)
  (hhf : forall x, 0 <= hf x) :
-- imply
  0 <= ghsiCovariance G K hf i j := by
-- proof
  apply StatMech.FrontierA.grahamInhomCov_nonneg G K hf hK hhf i j

/--
[grahamInhomAgreement_exp_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamAgreementVBGInhomogeneous.lean)
-/
@[path]
private lemma grahamInhomAgreement_exp_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {k : V}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  vbg_exp (ghsiAgreementProb G K hf) (vbg_coordUp k) = (1 + grahamInhomOne G K hf k ^ 2) / 2 := by
-- proof
  apply StatMech.FrontierA.grahamInhomAgreement_exp_eq G K hf k

/--
[grahamInhomAgreement_exp_mul_fibreT](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamAgreementVBGInhomogeneous.lean)
-/
@[path]
private lemma grahamInhomAgreement_exp_mul_fibreT_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {k : V}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  vbg_exp (ghsiAgreementProb G K hf) (fun q => vbg_coordUp k q * ghsiFibreT G K hf k q) = grahamInhomOne G K hf k := by
-- proof
  apply StatMech.FrontierA.grahamInhomAgreement_exp_mul_fibreT G K hf k

/--
[grahamInhomAgreement_exp_fibreT](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamAgreementVBGInhomogeneous.lean)
-/
@[path]
private lemma grahamInhomAgreement_exp_fibreT_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {k : V}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  vbg_exp (ghsiAgreementProb G K hf) (ghsiFibreT G K hf k) = grahamInhomOne G K hf k := by
-- proof
  apply StatMech.FrontierA.grahamInhomAgreement_exp_fibreT G K hf k

/--
[grahamInhomAgreement_exp_fibreUU](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamAgreementVBGInhomogeneous.lean)
-/
@[path]
private lemma grahamInhomAgreement_exp_fibreUU_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j : V}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  vbg_exp (ghsiAgreementProb G K hf) (ghsiFibreUU G K hf i j) = ghsiCovariance G K hf i j / 2 := by
-- proof
  apply StatMech.FrontierA.grahamInhomAgreement_exp_fibreUU G K hf i j

/--
[grahamInhomAgreement_exp_fibreUU_mul_fibreT](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamAgreementVBGInhomogeneous.lean)
-/
@[path]
private lemma grahamInhomAgreement_exp_fibreUU_mul_fibreT_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k : V}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  vbg_exp (ghsiAgreementProb G K hf) (fun q => ghsiFibreUU G K hf i j q * ghsiFibreT G K hf k q) = ghsiExp2 G K hf (fun a b => uvar a b i * uvar a b j * tvar a b k) := by
-- proof
  apply StatMech.FrontierA.grahamInhomAgreement_exp_fibreUU_mul_fibreT G K hf i j k

/--
[grahamInhomAgreement_cov_fibreUU_fibreT](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamAgreementVBGInhomogeneous.lean)
-/
@[path]
private lemma grahamInhomAgreement_cov_fibreUU_fibreT_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k : V}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  vbg_cov (ghsiAgreementProb G K hf) (ghsiFibreUU G K hf i j) (ghsiFibreT G K hf k) = ghsiUrsell3 G K hf i j k / 4 := by
-- proof
  apply StatMech.FrontierA.grahamInhomAgreement_cov_fibreUU_fibreT G K hf i j k

/--
[grahamInhomAgreement_exp_fibreUU_mul_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamAgreementVBGInhomogeneous.lean)
-/
@[path]
private lemma grahamInhomAgreement_exp_fibreUU_mul_agree_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k : V}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  vbg_exp (ghsiAgreementProb G K hf) (fun q => ghsiFibreUU G K hf i j q * vbg_coordUp k q) = ghsiExp2 G K hf (fun a b => (uvar a b i * uvar a b j) * grahamReplicaAgree a b k) := by
-- proof
  apply StatMech.FrontierA.grahamInhomAgreement_exp_fibreUU_mul_agree G K hf i j k

/--
[grahamInhomUUAgree_expansion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamAgreementVBGInhomogeneous.lean)
-/
@[path]
private lemma grahamInhomUUAgree_expansion_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k : V}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  ghsiExp2 G K hf (fun a b => (uvar a b i * uvar a b j) * grahamReplicaAgree a b k) = (ghsiCovariance G K hf i j + grahamInhomOne G K hf k * ghsiUrsell3 G K hf i j k - ghsiCovariance G K hf i k * ghsiCovariance G K hf j k + ghsiCovariance G K hf i j * grahamInhomOne G K hf k ^ 2) / 4 := by
-- proof
  apply StatMech.FrontierA.grahamInhomUUAgree_expansion G K hf i j k

/--
[grahamInhomAgreement_cov_fibreUU_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamAgreementVBGInhomogeneous.lean)
-/
@[path]
private lemma grahamInhomAgreement_cov_fibreUU_agree_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k : V}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  vbg_cov (ghsiAgreementProb G K hf) (ghsiFibreUU G K hf i j) (vbg_coordUp k) = (grahamInhomOne G K hf k * ghsiUrsell3 G K hf i j k - ghsiCovariance G K hf i k * ghsiCovariance G K hf j k) / 4 := by
-- proof
  apply StatMech.FrontierA.grahamInhomAgreement_cov_fibreUU_agree G K hf i j k

/--
[grahamInhomAgreement_cov_agree_fibreT](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamAgreementVBGInhomogeneous.lean)
-/
@[path]
private lemma grahamInhomAgreement_cov_agree_fibreT_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {k : V}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  vbg_cov (ghsiAgreementProb G K hf) (vbg_coordUp k) (ghsiFibreT G K hf k) = (1 - grahamInhomOne G K hf k ^ 2) * grahamInhomOne G K hf k / 2 := by
-- proof
  apply StatMech.FrontierA.grahamInhomAgreement_cov_agree_fibreT G K hf k

/--
[grahamInhomAgreement_var_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamAgreementVBGInhomogeneous.lean)
-/
@[path]
private lemma grahamInhomAgreement_var_agree_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {k : V}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  vbg_var (ghsiAgreementProb G K hf) (vbg_coordUp k) = (1 - grahamInhomOne G K hf k ^ 4) / 4 := by
-- proof
  apply StatMech.FrontierA.grahamInhomAgreement_var_agree G K hf k

/--
[grahamInhomAgreement_coord_pos_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamAgreementVBGInhomogeneous.lean)
-/
@[path]
private lemma grahamInhomAgreement_coord_pos_lt_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {k : V}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  0 < vbg_exp (ghsiAgreementProb G K hf) (vbg_coordUp k) /\ vbg_exp (ghsiAgreementProb G K hf) (vbg_coordUp k) < 1 := by
-- proof
  apply StatMech.FrontierA.grahamInhomAgreement_coord_pos_lt_one G K hf k

/--
[ghsiFibreUU_antitone_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamAgreementVBGInhomogeneous.lean)
-/
@[path]
private lemma ghsiFibreUU_antitone_all_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j : V}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real)
  (hK : forall e, 0 <= K e) :
-- imply
  Antitone (ghsiFibreUU G K hf i j) := by
-- proof
  apply StatMech.FrontierA.ghsiFibreUU_antitone_all G K hf hK i j

/--
[grahamAgreement_disagreement_product_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamAgreementVBGInhomogeneous.lean)
-/
@[path]
private lemma grahamAgreement_disagreement_product_lower_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k : V}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real)
  (hK : forall e, 0 <= K e)
  (hhf : forall x, 0 <= hf x) :
-- imply
  ghsiCovariance G K hf i k * ghsiCovariance G K hf j k <= 4 * vbg_exp (ghsiAgreementProb G K hf) (fun q => ghsiFibreUU G K hf i k q * ghsiFibreUU G K hf j k q) := by
-- proof
  apply StatMech.FrontierA.grahamAgreement_disagreement_product_lower G K hf hK hhf i j k

/--
[grahamImprovedGHS_inhomogeneous_strong](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamAgreementVBGInhomogeneous.lean)
-/
@[path]
private lemma grahamImprovedGHS_inhomogeneous_strong_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k : V}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real)
  (hK : forall e, 0 <= K e)
  (hhf : forall x, 0 <= hf x) :
-- imply
  (1 - grahamInhomOne G K hf k ^ 2) * (-ghsiUrsell3 G K hf i j k) >= 2 * grahamInhomOne G K hf k * ghsiCovariance G K hf i k * ghsiCovariance G K hf j k := by
-- proof
  apply StatMech.FrontierA.grahamImprovedGHS_inhomogeneous_strong G K hf hK hhf i j k

/--
[grahamImprovedGHS_inhomogeneous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamAgreementVBGInhomogeneous.lean)
-/
@[path]
private lemma grahamImprovedGHS_inhomogeneous_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k : V}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real)
  (hK : forall e, 0 <= K e)
  (hhf : forall x, 0 <= hf x) :
-- imply
  ghsiUrsell3 G K hf i j k <= -2 * ghsiCovariance G K hf i k * ghsiCovariance G K hf j k * grahamInhomOne G K hf k := by
-- proof
  apply StatMech.FrontierA.grahamImprovedGHS_inhomogeneous G K hf hK hhf i j k


-- created on 2026-10-23

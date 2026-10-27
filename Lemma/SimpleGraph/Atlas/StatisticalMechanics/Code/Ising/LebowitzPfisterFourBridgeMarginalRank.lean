import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeMarginalRank.Part3
open Finset SimpleGraph StatMech StatMech.Ising


/--
[agreementConfigFinsetEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeMarginalRank.lean)
-/
@[path]
private lemma agreementConfigFinsetEquiv_apply_eq
  [Fintype V]
  [DecidableEq V]
  {q : ConfigSpace V} :
-- imply
  agreementConfigFinsetEquiv q = ghsLAgreeFinset q := by
-- proof
  apply StatMech.Ising.agreementConfigFinsetEquiv_apply q

/--
[agreementConfigFinsetEquiv_symm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeMarginalRank.lean)
-/
@[path]
private lemma agreementConfigFinsetEquiv_symm_apply_eq
  [Fintype V]
  [DecidableEq V]
  {S : Finset V}
  {v : V} :
-- imply
  agreementConfigFinsetEquiv.symm S v = decide (v ∈ S) := by
-- proof
  apply StatMech.Ising.agreementConfigFinsetEquiv_symm_apply S v

/--
[ghsiSubsetMarginalMass_eq_common_mul_agreementMarginal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeMarginalRank.lean)
-/
@[path]
private lemma ghsiSubsetMarginalMass_eq_common_mul_agreementMarginal_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {M P : Finset V}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hPM : P ⊆ M) :
-- imply
  ghsiSubsetMarginalMass G J hf M P = ((4 * Fintype.card (ConfigSpace V) : Real) * (ZJ G.edgeFinset J hf) ^ 2) * ghsiAgreementMarginalProb G J hf M P := by
-- proof
  apply StatMech.Ising.ghsiSubsetMarginalMass_eq_common_mul_agreementMarginal G J hf hPM

/--
[replicaAgreementSpin_fourBridgeSites](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeMarginalRank.lean)
-/
@[path]
private lemma replicaAgreementSpin_fourBridgeSites_eq
  [Fintype V]
  [DecidableEq V]
  {q : ConfigSpace V}
  {w x y z : V} :
-- imply
  replicaAgreementSpin (fourBridgeSites w x y z) q = spin q w + spin q x + spin q y + spin q z := by
-- proof
  apply StatMech.Ising.replicaAgreementSpin_fourBridgeSites q w x y z

/--
[replicaBridgeInteraction_fourBridgeSites](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeMarginalRank.lean)
-/
@[path]
private lemma replicaBridgeInteraction_fourBridgeSites_eq
  [Fintype V]
  [DecidableEq V]
  {a b : ConfigSpace V}
  {w x y z : V} :
-- imply
  replicaBridgeInteraction (fourBridgeSites w x y z) a b = spin a w * spin b w + spin a x * spin b x + spin a y * spin b y + spin a z * spin b z := by
-- proof
  apply StatMech.Ising.replicaBridgeInteraction_fourBridgeSites a b w x y z

/--
[fourBridgeAgreementSpinMass_eq_ghsiExp2_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeMarginalRank.lean)
-/
@[path]
private lemma fourBridgeAgreementSpinMass_eq_ghsiExp2_indicator_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {w x y z : V}
  {s : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  fourBridgeAgreementSpinMass G J hf w x y z s = ghsiExp2 G J hf (fun a b => if replicaBridgeInteraction (fourBridgeSites w x y z) a b = s then 1 else 0) := by
-- proof
  apply StatMech.Ising.fourBridgeAgreementSpinMass_eq_ghsiExp2_indicator G J hf w x y z s

/--
[ghsiExp2_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeMarginalRank.lean)
-/
@[path]
private lemma ghsiExp2_sub_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (F H : ConfigSpace V -> ConfigSpace V -> Real) :
-- imply
  ghsiExp2 G J hf (fun a b => F a b - H a b) = ghsiExp2 G J hf F - ghsiExp2 G J hf H := by
-- proof
  apply StatMech.Ising.ghsiExp2_sub G J hf F H

/--
[ghsiExp2_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeMarginalRank.lean)
-/
@[path]
private lemma ghsiExp2_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  ghsiExp2 G J hf (fun _ _ => (1 : Real)) = 1 := by
-- proof
  apply StatMech.Ising.ghsiExp2_one G J hf

/--
[fourBridge_agree_inter_eq_empty_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeMarginalRank.lean)
-/
@[path]
private lemma fourBridge_agree_inter_eq_empty_iff_eq
  [Fintype V]
  [DecidableEq V]
  {q : ConfigSpace V}
  {w x y z : V} :
-- imply
  ghsLAgreeFinset q ∩ fourBridgeMarkedSet w x y z = ∅ ↔ q w = false ∧ q x = false ∧ q y = false ∧ q z = false := by
-- proof
  apply StatMech.Ising.fourBridge_agree_inter_eq_empty_iff q w x y z

/--
[fourBridge_agree_inter_eq_full_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeMarginalRank.lean)
-/
@[path]
private lemma fourBridge_agree_inter_eq_full_iff_eq
  [Fintype V]
  [DecidableEq V]
  {q : ConfigSpace V}
  {w x y z : V} :
-- imply
  ghsLAgreeFinset q ∩ fourBridgeMarkedSet w x y z = fourBridgeMarkedSet w x y z ↔ q w = true ∧ q x = true ∧ q y = true ∧ q z = true := by
-- proof
  apply StatMech.Ising.fourBridge_agree_inter_eq_full_iff q w x y z

/--
[ghsLAgreeFinset_inter_eq_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeMarginalRank.lean)
-/
@[path]
private lemma ghsLAgreeFinset_inter_eq_iff_eq
  [Fintype V]
  [DecidableEq V]
  {q : ConfigSpace V}
  {M P : Finset V} :
-- imply
  ghsLAgreeFinset q ∩ M = P ↔ P ⊆ M ∧ ∀ v ∈ M, (q v = true ↔ v ∈ P) := by
-- proof
  apply StatMech.Ising.ghsLAgreeFinset_inter_eq_iff q M P

/--
[fourBridge_agree_inter_eq_singleton_w_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeMarginalRank.lean)
-/
@[path]
private lemma fourBridge_agree_inter_eq_singleton_w_iff_eq
  [Fintype V]
  [DecidableEq V]
  {q : ConfigSpace V}
  {w x y z : V}
-- given
  (hwx : w ≠ x)
  (hwy : w ≠ y)
  (hwz : w ≠ z)
  (hxy : x ≠ y)
  (hxz : x ≠ z)
  (hyz : y ≠ z) :
-- imply
  ghsLAgreeFinset q ∩ fourBridgeMarkedSet w x y z = {w} ↔ q w = true ∧ q x = false ∧ q y = false ∧ q z = false := by
-- proof
  apply StatMech.Ising.fourBridge_agree_inter_eq_singleton_w_iff q hwx hwy hwz hxy hxz hyz

/--
[fourBridge_agree_inter_eq_singleton_x_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeMarginalRank.lean)
-/
@[path]
private lemma fourBridge_agree_inter_eq_singleton_x_iff_eq
  [Fintype V]
  [DecidableEq V]
  {q : ConfigSpace V}
  {w x y z : V}
-- given
  (hwx : w ≠ x)
  (hwy : w ≠ y)
  (hwz : w ≠ z)
  (hxy : x ≠ y)
  (hxz : x ≠ z)
  (hyz : y ≠ z) :
-- imply
  ghsLAgreeFinset q ∩ fourBridgeMarkedSet w x y z = {x} ↔ q w = false ∧ q x = true ∧ q y = false ∧ q z = false := by
-- proof
  apply StatMech.Ising.fourBridge_agree_inter_eq_singleton_x_iff q hwx hwy hwz hxy hxz hyz

/--
[fourBridge_agree_inter_eq_singleton_y_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeMarginalRank.lean)
-/
@[path]
private lemma fourBridge_agree_inter_eq_singleton_y_iff_eq
  [Fintype V]
  [DecidableEq V]
  {q : ConfigSpace V}
  {w x y z : V}
-- given
  (hwx : w ≠ x)
  (hwy : w ≠ y)
  (hwz : w ≠ z)
  (hxy : x ≠ y)
  (hxz : x ≠ z)
  (hyz : y ≠ z) :
-- imply
  ghsLAgreeFinset q ∩ fourBridgeMarkedSet w x y z = {y} ↔ q w = false ∧ q x = false ∧ q y = true ∧ q z = false := by
-- proof
  apply StatMech.Ising.fourBridge_agree_inter_eq_singleton_y_iff q hwx hwy hwz hxy hxz hyz

/--
[fourBridge_agree_inter_eq_singleton_z_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeMarginalRank.lean)
-/
@[path]
private lemma fourBridge_agree_inter_eq_singleton_z_iff_eq
  [Fintype V]
  [DecidableEq V]
  {q : ConfigSpace V}
  {w x y z : V}
-- given
  (hwx : w ≠ x)
  (hwy : w ≠ y)
  (hwz : w ≠ z)
  (hxy : x ≠ y)
  (hxz : x ≠ z)
  (hyz : y ≠ z) :
-- imply
  ghsLAgreeFinset q ∩ fourBridgeMarkedSet w x y z = {z} ↔ q w = false ∧ q x = false ∧ q y = false ∧ q z = true := by
-- proof
  apply StatMech.Ising.fourBridge_agree_inter_eq_singleton_z_iff q hwx hwy hwz hxy hxz hyz

/--
[fourBridge_agree_inter_eq_cosingleton_w_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeMarginalRank.lean)
-/
@[path]
private lemma fourBridge_agree_inter_eq_cosingleton_w_iff_eq
  [Fintype V]
  [DecidableEq V]
  {q : ConfigSpace V}
  {w x y z : V}
-- given
  (hwx : w ≠ x)
  (hwy : w ≠ y)
  (hwz : w ≠ z)
  (hxy : x ≠ y)
  (hxz : x ≠ z)
  (hyz : y ≠ z) :
-- imply
  ghsLAgreeFinset q ∩ fourBridgeMarkedSet w x y z = fourBridgeMarkedSet w x y z \ {w} ↔ q w = false ∧ q x = true ∧ q y = true ∧ q z = true := by
-- proof
  apply StatMech.Ising.fourBridge_agree_inter_eq_cosingleton_w_iff q hwx hwy hwz hxy hxz hyz

/--
[fourBridge_agree_inter_eq_cosingleton_x_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeMarginalRank.lean)
-/
@[path]
private lemma fourBridge_agree_inter_eq_cosingleton_x_iff_eq
  [Fintype V]
  [DecidableEq V]
  {q : ConfigSpace V}
  {w x y z : V}
-- given
  (hwx : w ≠ x)
  (hwy : w ≠ y)
  (hwz : w ≠ z)
  (hxy : x ≠ y)
  (hxz : x ≠ z)
  (hyz : y ≠ z) :
-- imply
  ghsLAgreeFinset q ∩ fourBridgeMarkedSet w x y z = fourBridgeMarkedSet w x y z \ {x} ↔ q w = true ∧ q x = false ∧ q y = true ∧ q z = true := by
-- proof
  apply StatMech.Ising.fourBridge_agree_inter_eq_cosingleton_x_iff q hwx hwy hwz hxy hxz hyz

/--
[fourBridge_agree_inter_eq_cosingleton_y_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeMarginalRank.lean)
-/
@[path]
private lemma fourBridge_agree_inter_eq_cosingleton_y_iff_eq
  [Fintype V]
  [DecidableEq V]
  {q : ConfigSpace V}
  {w x y z : V}
-- given
  (hwx : w ≠ x)
  (hwy : w ≠ y)
  (hwz : w ≠ z)
  (hxy : x ≠ y)
  (hxz : x ≠ z)
  (hyz : y ≠ z) :
-- imply
  ghsLAgreeFinset q ∩ fourBridgeMarkedSet w x y z = fourBridgeMarkedSet w x y z \ {y} ↔ q w = true ∧ q x = true ∧ q y = false ∧ q z = true := by
-- proof
  apply StatMech.Ising.fourBridge_agree_inter_eq_cosingleton_y_iff q hwx hwy hwz hxy hxz hyz

/--
[fourBridge_agree_inter_eq_cosingleton_z_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeMarginalRank.lean)
-/
@[path]
private lemma fourBridge_agree_inter_eq_cosingleton_z_iff_eq
  [Fintype V]
  [DecidableEq V]
  {q : ConfigSpace V}
  {w x y z : V}
-- given
  (hwx : w ≠ x)
  (hwy : w ≠ y)
  (hwz : w ≠ z)
  (hxy : x ≠ y)
  (hxz : x ≠ z)
  (hyz : y ≠ z) :
-- imply
  ghsLAgreeFinset q ∩ fourBridgeMarkedSet w x y z = fourBridgeMarkedSet w x y z \ {z} ↔ q w = true ∧ q x = true ∧ q y = true ∧ q z = false := by
-- proof
  apply StatMech.Ising.fourBridge_agree_inter_eq_cosingleton_z_iff q hwx hwy hwz hxy hxz hyz

/--
[fourBridgeAgreementSpinMass_neg_four_eq_marginal_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeMarginalRank.lean)
-/
@[path]
private lemma fourBridgeAgreementSpinMass_neg_four_eq_marginal_empty_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {w x y z : V}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  fourBridgeAgreementSpinMass G J hf w x y z (-4) = ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) ∅ := by
-- proof
  apply StatMech.Ising.fourBridgeAgreementSpinMass_neg_four_eq_marginal_empty G J hf w x y z

/--
[fourBridgeAgreementSpinMass_four_eq_marginal_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeMarginalRank.lean)
-/
@[path]
private lemma fourBridgeAgreementSpinMass_four_eq_marginal_full_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {w x y z : V}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  fourBridgeAgreementSpinMass G J hf w x y z 4 = ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) (fourBridgeMarkedSet w x y z) := by
-- proof
  apply StatMech.Ising.fourBridgeAgreementSpinMass_four_eq_marginal_full G J hf w x y z

/--
[fourBridgeAgreementSpinMass_neg_two_eq_marginal_singletons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeMarginalRank.lean)
-/
@[path]
private lemma fourBridgeAgreementSpinMass_neg_two_eq_marginal_singletons_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {w x y z : V}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hwx : w ≠ x)
  (hwy : w ≠ y)
  (hwz : w ≠ z)
  (hxy : x ≠ y)
  (hxz : x ≠ z)
  (hyz : y ≠ z) :
-- imply
  fourBridgeAgreementSpinMass G J hf w x y z (-2) = ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) {w} + ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) {x} + ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) {y} + ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) {z} := by
-- proof
  apply StatMech.Ising.fourBridgeAgreementSpinMass_neg_two_eq_marginal_singletons G J hf hwx hwy hwz hxy hxz hyz

/--
[fourBridgeAgreementSpinMass_two_eq_marginal_cosingletons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeMarginalRank.lean)
-/
@[path]
private lemma fourBridgeAgreementSpinMass_two_eq_marginal_cosingletons_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {w x y z : V}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hwx : w ≠ x)
  (hwy : w ≠ y)
  (hwz : w ≠ z)
  (hxy : x ≠ y)
  (hxz : x ≠ z)
  (hyz : y ≠ z) :
-- imply
  fourBridgeAgreementSpinMass G J hf w x y z 2 = ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) (fourBridgeMarkedSet w x y z \ {w}) + ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) (fourBridgeMarkedSet w x y z \ {x}) + ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) (fourBridgeMarkedSet w x y z \ {y}) + ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) (fourBridgeMarkedSet w x y z \ {z}) := by
-- proof
  apply StatMech.Ising.fourBridgeAgreementSpinMass_two_eq_marginal_cosingletons G J hf hwx hwy hwz hxy hxz hyz

/--
[fourBridgeAgreementSpinMass_neg_four_eq_rankMass_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeMarginalRank.lean)
-/
@[path]
private lemma fourBridgeAgreementSpinMass_neg_four_eq_rankMass_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {w x y z : V}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  fourBridgeAgreementSpinMass G J hf w x y z (-4) = fourBridgeRankMass (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) 0 := by
-- proof
  apply StatMech.Ising.fourBridgeAgreementSpinMass_neg_four_eq_rankMass_zero G J hf w x y z

/--
[fourBridgeAgreementSpinMass_four_eq_rankMass_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeMarginalRank.lean)
-/
@[path]
private lemma fourBridgeAgreementSpinMass_four_eq_rankMass_four_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {w x y z : V}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  fourBridgeAgreementSpinMass G J hf w x y z 4 = fourBridgeRankMass (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) 4 := by
-- proof
  apply StatMech.Ising.fourBridgeAgreementSpinMass_four_eq_rankMass_four G J hf w x y z

/--
[fourBridgeAgreementSpinMass_neg_two_eq_rankMass_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeMarginalRank.lean)
-/
@[path]
private lemma fourBridgeAgreementSpinMass_neg_two_eq_rankMass_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {w x y z : V}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  fourBridgeAgreementSpinMass G J hf w x y z (-2) = fourBridgeRankMass (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) 1 := by
-- proof
  apply StatMech.Ising.fourBridgeAgreementSpinMass_neg_two_eq_rankMass_one G J hf w x y z

/--
[fourBridgeAgreementSpinMass_two_eq_rankMass_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeMarginalRank.lean)
-/
@[path]
private lemma fourBridgeAgreementSpinMass_two_eq_rankMass_three_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {w x y z : V}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  fourBridgeAgreementSpinMass G J hf w x y z 2 = fourBridgeRankMass (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) 3 := by
-- proof
  apply StatMech.Ising.fourBridgeAgreementSpinMass_two_eq_rankMass_three G J hf w x y z

/--
[fourBridgeRankMass_rankCross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeMarginalRank.lean)
-/
@[path]
private lemma fourBridgeRankMass_rankCross_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {w x y z : V}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hJ : ∀ e, 0 ≤ J e)
  (hhf : ∀ v, 0 ≤ hf v)
  (hwx : w ≠ x)
  (hwy : w ≠ y)
  (hwz : w ≠ z)
  (hxy : x ≠ y)
  (hxz : x ≠ z)
  (hyz : y ≠ z) :
-- imply
  fourBridgeRankMass (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) 0 * fourBridgeRankMass (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) 3 ≤ fourBridgeRankMass (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) 1 * fourBridgeRankMass (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) 4 := by
-- proof
  apply StatMech.Ising.fourBridgeRankMass_rankCross G J hf hJ hhf hwx hwy hwz hxy hxz hyz

/--
[fourBridgeVarianceSkewBernsteinCoeff_five_six_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeMarginalRank.lean)
-/
@[path]
private lemma fourBridgeVarianceSkewBernsteinCoeff_five_six_nonpos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {w x y z : V}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hJ : ∀ e, 0 ≤ J e)
  (hhf : ∀ v, 0 ≤ hf v)
  (hwx : w ≠ x)
  (hwy : w ≠ y)
  (hwz : w ≠ z)
  (hxy : x ≠ y)
  (hxz : x ≠ z)
  (hyz : y ≠ z) :
-- imply
  fourBridgeVarianceSkewBernsteinCoeff (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) 5 ≤ 0 ∧ fourBridgeVarianceSkewBernsteinCoeff (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) 6 ≤ 0 := by
-- proof
  apply StatMech.Ising.fourBridgeVarianceSkewBernsteinCoeff_five_six_nonpos G J hf hJ hhf hwx hwy hwz hxy hxz hyz


-- created on 2026-10-23

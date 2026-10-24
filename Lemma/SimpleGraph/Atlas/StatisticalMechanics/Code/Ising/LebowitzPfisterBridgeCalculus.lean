import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.LebowitzPfisterBridgeCalculus
open Finset Filter StatMech StatMech.Ising


/--
[replicaBridgeInteraction_mate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterBridgeCalculus.lean)
-/
@[path]
private lemma replicaBridgeInteraction_mate_eq
  [Fintype V]
  [DecidableEq V]
  {q a : ConfigSpace V}
-- given
  (sites : I -> V) :
-- imply
  replicaBridgeInteraction sites a (ghsLMate q a) = replicaAgreementSpin sites q := by
-- proof
  apply StatMech.Ising.replicaBridgeInteraction_mate sites q a

/--
[replicaBridgeMoment_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterBridgeCalculus.lean)
-/
@[path]
private lemma replicaBridgeMoment_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (sites : I -> V) :
-- imply
  0 < replicaBridgeMoment G J hf sites r := by
-- proof
  apply StatMech.Ising.replicaBridgeMoment_pos G J hf sites r

/--
[replicaBridgeMoment_eq_agreementTilt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterBridgeCalculus.lean)
-/
@[path]
private lemma replicaBridgeMoment_eq_agreementTilt_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (sites : I -> V) :
-- imply
  replicaBridgeMoment G J hf sites r = ∑ q : ConfigSpace V, ghsiAgreementProb G J hf q * Real.exp (r * replicaAgreementSpin sites q) := by
-- proof
  apply StatMech.Ising.replicaBridgeMoment_eq_agreementTilt G J hf sites r

/--
[ghsiExp2_replicaBridgeFunction_eq_agreement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterBridgeCalculus.lean)
-/
@[path]
private lemma ghsiExp2_replicaBridgeFunction_eq_agreement_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (sites : I -> V)
  (F : Real -> Real) :
-- imply
  ghsiExp2 G J hf (fun a b => F (replicaBridgeInteraction sites a b)) = ∑ q : ConfigSpace V, ghsiAgreementProb G J hf q * F (replicaAgreementSpin sites q) := by
-- proof
  apply StatMech.Ising.ghsiExp2_replicaBridgeFunction_eq_agreement G J hf sites F

/--
[replicaAgreementTiltProb_sum_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterBridgeCalculus.lean)
-/
@[path]
private lemma replicaAgreementTiltProb_sum_eq_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (sites : I -> V) :
-- imply
  ∑ q : ConfigSpace V, replicaAgreementTiltProb G J hf sites r q = 1 := by
-- proof
  apply StatMech.Ising.replicaAgreementTiltProb_sum_eq_one G J hf sites r

/--
[replicaBridgeMean_eq_agreementTiltMean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterBridgeCalculus.lean)
-/
@[path]
private lemma replicaBridgeMean_eq_agreementTiltMean_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (sites : I -> V) :
-- imply
  replicaBridgeMean G J hf sites r = ∑ q : ConfigSpace V, replicaAgreementTiltProb G J hf sites r q * replicaAgreementSpin sites q := by
-- proof
  apply StatMech.Ising.replicaBridgeMean_eq_agreementTiltMean G J hf sites r

/--
[replicaBridgeVariance_eq_agreementTiltVariance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterBridgeCalculus.lean)
-/
@[path]
private lemma replicaBridgeVariance_eq_agreementTiltVariance_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (sites : I -> V) :
-- imply
  replicaBridgeVariance G J hf sites r = replicaAgreementTiltVariance G J hf sites r := by
-- proof
  apply StatMech.Ising.replicaBridgeVariance_eq_agreementTiltVariance G J hf sites r

/--
[ghsiExp2_finset_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterBridgeCalculus.lean)
-/
@[path]
private lemma ghsiExp2_finset_sum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset A}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (F : A -> ConfigSpace V -> ConfigSpace V -> Real) :
-- imply
  ghsiExp2 G J hf (fun a b => ∑ i ∈ S, F i a b) = ∑ i ∈ S, ghsiExp2 G J hf (F i) := by
-- proof
  apply StatMech.Ising.ghsiExp2_finset_sum G J hf S F

/--
[replicaBridgeMoment_highTemp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterBridgeCalculus.lean)
-/
@[path]
private lemma replicaBridgeMoment_highTemp_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (sites : I -> V) :
-- imply
  replicaBridgeMoment G J hf sites r = ∑ S ∈ (Finset.univ : Finset I).powerset, Real.sinh r ^ S.card * Real.cosh r ^ (Fintype.card I - S.card) * (expJ G.edgeFinset J hf (replicaBridgeMonomial sites S)) ^ 2 := by
-- proof
  apply StatMech.Ising.replicaBridgeMoment_highTemp G J hf sites r

/--
[hasDerivAt_replicaBridgeMoment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterBridgeCalculus.lean)
-/
@[path]
private lemma hasDerivAt_replicaBridgeMoment_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (sites : I -> V) :
-- imply
  HasDerivAt (replicaBridgeMoment G J hf sites) (ghsiExp2 G J hf (fun a b => replicaBridgeInteraction sites a b * Real.exp (r * replicaBridgeInteraction sites a b))) r := by
-- proof
  apply StatMech.Ising.hasDerivAt_replicaBridgeMoment G J hf sites r

/--
[hasDerivAt_replicaBridgeWeightedMeanNumerator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterBridgeCalculus.lean)
-/
@[path]
private lemma hasDerivAt_replicaBridgeWeightedMeanNumerator_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (sites : I -> V) :
-- imply
  HasDerivAt (fun t => ghsiExp2 G J hf (fun a b => replicaBridgeInteraction sites a b * Real.exp (t * replicaBridgeInteraction sites a b))) (ghsiExp2 G J hf (fun a b => replicaBridgeInteraction sites a b ^ 2 * Real.exp (r * replicaBridgeInteraction sites a b))) r := by
-- proof
  apply StatMech.Ising.hasDerivAt_replicaBridgeWeightedMeanNumerator G J hf sites r

/--
[hasDerivAt_replicaBridgeMean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterBridgeCalculus.lean)
-/
@[path]
private lemma hasDerivAt_replicaBridgeMean_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (sites : I -> V) :
-- imply
  HasDerivAt (replicaBridgeMean G J hf sites) (replicaBridgeVariance G J hf sites r) r := by
-- proof
  apply StatMech.Ising.hasDerivAt_replicaBridgeMean G J hf sites r

/--
[hasDerivAt_replicaBridgeSymmetricMean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterBridgeCalculus.lean)
-/
@[path]
private lemma hasDerivAt_replicaBridgeSymmetricMean_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (sites : I -> V) :
-- imply
  HasDerivAt (fun t => replicaBridgeMean G J hf sites t + replicaBridgeMean G J hf sites (-t)) (replicaBridgeVariance G J hf sites r - replicaBridgeVariance G J hf sites (-r)) r := by
-- proof
  apply StatMech.Ising.hasDerivAt_replicaBridgeSymmetricMean G J hf sites r

/--
[hasDerivAt_log_replicaBridgeMoment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterBridgeCalculus.lean)
-/
@[path]
private lemma hasDerivAt_log_replicaBridgeMoment_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (sites : I -> V) :
-- imply
  HasDerivAt (fun t => Real.log (replicaBridgeMoment G J hf sites t)) (replicaBridgeMean G J hf sites r) r := by
-- proof
  apply StatMech.Ising.hasDerivAt_log_replicaBridgeMoment G J hf sites r

/--
[hasDerivAt_replicaBridgeFreeEnergy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterBridgeCalculus.lean)
-/
@[path]
private lemma hasDerivAt_replicaBridgeFreeEnergy_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (sites : I -> V) :
-- imply
  HasDerivAt (replicaBridgeFreeEnergy G J hf sites) (replicaBridgeMean G J hf sites r + replicaBridgeMean G J hf sites (-r)) r := by
-- proof
  apply StatMech.Ising.hasDerivAt_replicaBridgeFreeEnergy G J hf sites r

/--
[replicaBridgeMean_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterBridgeCalculus.lean)
-/
@[path]
private lemma replicaBridgeMean_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (sites : I -> V) :
-- imply
  replicaBridgeMean G J hf sites 0 = ∑ i : I, (expJ G.edgeFinset J hf (fun s => spin s (sites i))) ^ 2 := by
-- proof
  apply StatMech.Ising.replicaBridgeMean_zero G J hf sites

/--
[replicaBridgeFreeEnergy_deriv_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterBridgeCalculus.lean)
-/
@[path]
private lemma replicaBridgeFreeEnergy_deriv_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (sites : I -> V) :
-- imply
  deriv (replicaBridgeFreeEnergy G J hf sites) 0 = 2 * ∑ i : I, (expJ G.edgeFinset J hf (fun s => spin s (sites i))) ^ 2 := by
-- proof
  apply StatMech.Ising.replicaBridgeFreeEnergy_deriv_zero G J hf sites

/--
[replicaBridgeSymmetricMean_le_zero_of_variance_order](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterBridgeCalculus.lean)
-/
@[path]
private lemma replicaBridgeSymmetricMean_le_zero_of_variance_order_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (sites : I -> V)
  (hr : 0 <= r)
  (hvar : forall t, 0 <= t -> replicaBridgeVariance G J hf sites t <= replicaBridgeVariance G J hf sites (-t)) :
-- imply
  replicaBridgeMean G J hf sites r + replicaBridgeMean G J hf sites (-r) <= 2 * replicaBridgeMean G J hf sites 0 := by
-- proof
  apply StatMech.Ising.replicaBridgeSymmetricMean_le_zero_of_variance_order G J hf sites r hr hvar

/--
[replicaBridgeFreeEnergy_le_of_symmetric_mean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterBridgeCalculus.lean)
-/
@[path]
private lemma replicaBridgeFreeEnergy_le_of_symmetric_mean_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (sites : I -> V)
  (hr : 0 ≤ r)
  (hmean : ∀ t, 0 ≤ t -> replicaBridgeMean G J hf sites t + replicaBridgeMean G J hf sites (-t) ≤ 2 * replicaBridgeMean G J hf sites 0) :
-- imply
  replicaBridgeFreeEnergy G J hf sites r ≤ 2 * r * ∑ i : I, (expJ G.edgeFinset J hf (fun s => spin s (sites i))) ^ 2 := by
-- proof
  apply StatMech.Ising.replicaBridgeFreeEnergy_le_of_symmetric_mean G J hf sites r hr hmean

/--
[replicaBridgeFreeEnergy_le_of_variance_order](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterBridgeCalculus.lean)
-/
@[path]
private lemma replicaBridgeFreeEnergy_le_of_variance_order_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (sites : I -> V)
  (hr : 0 <= r)
  (hvar : forall t, 0 <= t -> replicaBridgeVariance G J hf sites t <= replicaBridgeVariance G J hf sites (-t)) :
-- imply
  replicaBridgeFreeEnergy G J hf sites r <= 2 * r * ∑ i : I, (expJ G.edgeFinset J hf (fun s => spin s (sites i))) ^ 2 := by
-- proof
  apply StatMech.Ising.replicaBridgeFreeEnergy_le_of_variance_order G J hf sites r hr hvar


-- created on 2026-10-23

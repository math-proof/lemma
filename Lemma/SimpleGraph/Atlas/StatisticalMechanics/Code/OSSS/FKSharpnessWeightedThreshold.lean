import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedThreshold
open Finset Set Filter Topology MeasureTheory StatMech StatMech.OSSS StatMech.OSSS.FKSharpnessWeightedThreshold


/--
[weightedPhaseSharpConstant_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedThreshold.lean)
-/
@[path]
private lemma weightedPhaseSharpConstant_pos_eq
  {d : Nat}
  {Jmin Jmax beta0 : Real}
-- given
  (hJmin : 0 < Jmin) :
-- imply
  0 < weightedPhaseSharpConstant d Jmin Jmax beta0 := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedThreshold.weightedPhaseSharpConstant_pos d hJmin

/--
[weightedSelectedPhaseSum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedThreshold.lean)
-/
@[path]
private lemma weightedSelectedPhaseSum_nonneg_eq
  {d : Nat}
  [Fintype P]
  {q : Real}
  {beta : Real}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall a e, 0 < phaseJ a e)
  (hq : 0 < q) :
-- imply
  0 <= weightedSelectedPhaseSum d phaseJ hJ q hq beta := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedThreshold.weightedSelectedPhaseSum_nonneg d phaseJ hJ q hq beta

/--
[weightedPhaseSum_tendsto_selectedPhaseSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedThreshold.lean)
-/
@[path]
private lemma weightedPhaseSum_tendsto_selectedPhaseSum_eq
  {d : Nat}
  [Fintype P]
  {q beta : Real}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall a e, 0 < phaseJ a e)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  Tendsto (fun n => weightedPhaseSum d phaseJ q beta n) atTop (nhds (weightedSelectedPhaseSum d phaseJ hJ q (zero_lt_one.trans_le hq) beta)) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedThreshold.weightedPhaseSum_tendsto_selectedPhaseSum d phaseJ hJ q beta hq hbeta

/--
[weightedNormalizedPhaseSum_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedThreshold.lean)
-/
@[path]
private lemma weightedNormalizedPhaseSum_tendsto_eq
  {d : Nat}
  [Fintype P]
  {Jmin Jmax q beta0 beta : Real}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall a e, 0 < phaseJ a e)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  Tendsto (fun n => weightedNormalizedPhaseSum d phaseJ Jmin Jmax q beta0 n beta) atTop (nhds (weightedSelectedPhaseSum d phaseJ hJ q (zero_lt_one.trans_le hq) beta / weightedPhaseSharpConstant d Jmin Jmax beta0)) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedThreshold.weightedNormalizedPhaseSum_tendsto d phaseJ hJ Jmin Jmax q beta0 beta hq hbeta

/--
[weightedNormalizedPhaseSum_meanLogTerm_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedThreshold.lean)
-/
@[path]
private lemma weightedNormalizedPhaseSum_meanLogTerm_tendsto_eq
  {d : Nat}
  [Fintype P]
  {Jmin Jmax q beta0 beta : Real}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall a e, 0 < phaseJ a e)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  Tendsto (fun n => Integration.meanLogTerm (weightedNormalizedPhaseSum d phaseJ Jmin Jmax q beta0) n beta) atTop (nhds (weightedSelectedPhaseSum d phaseJ hJ q (zero_lt_one.trans_le hq) beta / weightedPhaseSharpConstant d Jmin Jmax beta0)) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedThreshold.weightedNormalizedPhaseSum_meanLogTerm_tendsto d phaseJ hJ Jmin Jmax q beta0 beta hq hbeta

/--
[weightedThresholdPhaseSum_of_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedThreshold.lean)
-/
@[path]
private lemma weightedThresholdPhaseSum_of_pos_eq
  {d n : Nat}
  [Fintype P]
  {Jmin Jmax q beta0 beta : Real}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hbeta : 0 < beta) :
-- imply
  weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0 n beta = weightedNormalizedPhaseSum d phaseJ Jmin Jmax q beta0 n beta := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedThreshold.weightedThresholdPhaseSum_of_pos d n phaseJ Jmin Jmax q beta0 beta hbeta

/--
[weightedNormalizedPhaseSumSig_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedThreshold.lean)
-/
@[path]
private lemma weightedNormalizedPhaseSumSig_eq_eq
  {d n : Nat}
  [Fintype P]
  {Jmin Jmax q beta0 beta : Real}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real) :
-- imply
  Sig (weightedNormalizedPhaseSum d phaseJ Jmin Jmax q beta0) n beta = weightedPhaseSumSig d n phaseJ q beta / weightedPhaseSharpConstant d Jmin Jmax beta0 := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedThreshold.weightedNormalizedPhaseSumSig_eq d n phaseJ Jmin Jmax q beta0 beta

/--
[weightedPhaseSum_differentiableAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedThreshold.lean)
-/
@[path]
private lemma weightedPhaseSum_differentiableAt_eq
  {d n : Nat}
  [Fintype P]
  {q beta : Real}
-- given
  (hn : 1 <= n)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall a e, 0 < phaseJ a e)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  DifferentiableAt Real (fun b => weightedPhaseSum d phaseJ q b n) beta := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedThreshold.weightedPhaseSum_differentiableAt d n hn phaseJ hJ q beta hq hbeta

/--
[weightedNormalizedPhaseSum_hasDerivAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedThreshold.lean)
-/
@[path]
private lemma weightedNormalizedPhaseSum_hasDerivAt_eq
  {d n : Nat}
  [Fintype P]
  {Jmin Jmax q beta0 beta : Real}
-- given
  (hn : 1 <= n)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall a e, 0 < phaseJ a e)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  HasDerivAt (weightedNormalizedPhaseSum d phaseJ Jmin Jmax q beta0 n) (weightedNormalizedPhaseSumPrime d phaseJ Jmin Jmax q beta0 n beta) beta := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedThreshold.weightedNormalizedPhaseSum_hasDerivAt d n hn phaseJ hJ Jmin Jmax q beta0 beta hq hbeta

/--
[weightedNormalizedPhaseSum_differential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedThreshold.lean)
-/
@[path]
private lemma weightedNormalizedPhaseSum_differential_eq
  {d n : Nat}
  [Fintype P]
  [Nonempty P]
  {Jmin Jmax : Real}
  {q beta beta0 : Real}
-- given
  (hn : 1 <= n)
  (J : Sym2 (Site d) -> Real)
  (hJmin : 0 < Jmin)
  (hJlo : forall e, Jmin <= J e)
  (hJhi : forall e, J e <= Jmax)
  (phase : Site d -> P)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hsurj : Function.Surjective phase)
  (hcov : PhaseCovariant J phase phaseJ)
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hbeta0 : beta <= beta0) :
-- imply
  (((n : Real) / Sig (weightedNormalizedPhaseSum d phaseJ Jmin Jmax q beta0) n beta) * weightedNormalizedPhaseSum d phaseJ Jmin Jmax q beta0 n beta) <= weightedNormalizedPhaseSumPrime d phaseJ Jmin Jmax q beta0 n beta := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedThreshold.weightedNormalizedPhaseSum_differential d n hn J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov q beta beta0 hq hbeta hbeta0

/--
[weightedPhaseProfile_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedThreshold.lean)
-/
@[path]
private lemma weightedPhaseProfile_le_one_eq
  {d n : Nat}
  {a : P}
  {q beta : Real}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall a e, 0 < phaseJ a e)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  weightedPhaseProfile d phaseJ a q beta n <= 1 := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedThreshold.weightedPhaseProfile_le_one d n phaseJ hJ a q beta hq hbeta

/--
[weightedPhaseSum_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedThreshold.lean)
-/
@[path]
private lemma weightedPhaseSum_zero_eq
  {d : Nat}
  [Fintype P]
  {q beta : Real}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real) :
-- imply
  weightedPhaseSum d phaseJ q beta 0 = Fintype.card P := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedThreshold.weightedPhaseSum_zero d phaseJ q beta

/--
[weightedPhaseSum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedThreshold.lean)
-/
@[path]
private lemma weightedPhaseSum_nonneg_eq
  {d n : Nat}
  [Fintype P]
  {q beta : Real}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall a e, 0 < phaseJ a e)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  0 <= weightedPhaseSum d phaseJ q beta n := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedThreshold.weightedPhaseSum_nonneg d n phaseJ hJ q beta hq hbeta

/--
[weightedPhaseSum_le_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedThreshold.lean)
-/
@[path]
private lemma weightedPhaseSum_le_card_eq
  {d n : Nat}
  [Fintype P]
  {q beta : Real}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall a e, 0 < phaseJ a e)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  weightedPhaseSum d phaseJ q beta n <= Fintype.card P := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedThreshold.weightedPhaseSum_le_card d n phaseJ hJ q beta hq hbeta

/--
[weightedPhaseSumSig_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedThreshold.lean)
-/
@[path]
private lemma weightedPhaseSumSig_pos_eq
  {d n : Nat}
  [Fintype P]
  [Nonempty P]
  {q beta : Real}
-- given
  (hn : 1 <= n)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall a e, 0 < phaseJ a e)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  0 < weightedPhaseSumSig d n phaseJ q beta := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedThreshold.weightedPhaseSumSig_pos d n hn phaseJ hJ q beta hq hbeta

/--
[weightedNormalizedPhaseSum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedThreshold.lean)
-/
@[path]
private lemma weightedNormalizedPhaseSum_nonneg_eq
  {d n : Nat}
  [Fintype P]
  {Jmin Jmax q beta0 beta : Real}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall a e, 0 < phaseJ a e)
  (hJmin : 0 < Jmin)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  0 <= weightedNormalizedPhaseSum d phaseJ Jmin Jmax q beta0 n beta := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedThreshold.weightedNormalizedPhaseSum_nonneg d n phaseJ hJ Jmin Jmax q beta0 beta hJmin hq hbeta

/--
[weightedNormalizedPhaseSum_le_card_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedThreshold.lean)
-/
@[path]
private lemma weightedNormalizedPhaseSum_le_card_div_eq
  {d n : Nat}
  [Fintype P]
  {Jmin Jmax q beta0 beta : Real}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall a e, 0 < phaseJ a e)
  (hJmin : 0 < Jmin)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  weightedNormalizedPhaseSum d phaseJ Jmin Jmax q beta0 n beta <= (Fintype.card P : Real) / weightedPhaseSharpConstant d Jmin Jmax beta0 := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedThreshold.weightedNormalizedPhaseSum_le_card_div d n phaseJ hJ Jmin Jmax q beta0 beta hJmin hq hbeta

/--
[weightedNormalizedPhaseSumPrime_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedThreshold.lean)
-/
@[path]
private lemma weightedNormalizedPhaseSumPrime_nonneg_eq
  {d n : Nat}
  [Fintype P]
  [Nonempty P]
  {Jmin Jmax : Real}
  {q beta beta0 : Real}
-- given
  (hn : 1 <= n)
  (J : Sym2 (Site d) -> Real)
  (hJmin : 0 < Jmin)
  (hJlo : forall e, Jmin <= J e)
  (hJhi : forall e, J e <= Jmax)
  (phase : Site d -> P)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hsurj : Function.Surjective phase)
  (hcov : PhaseCovariant J phase phaseJ)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  0 <= weightedNormalizedPhaseSumPrime d phaseJ Jmin Jmax q beta0 n beta := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedThreshold.weightedNormalizedPhaseSumPrime_nonneg d n hn J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov q beta beta0 hq hbeta

/--
[weightedNormalizedPhaseSum_mono_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedThreshold.lean)
-/
@[path]
private lemma weightedNormalizedPhaseSum_mono_beta_eq
  {d n : Nat}
  [Fintype P]
  [Nonempty P]
  {Jmin Jmax : Real}
  {q beta0 y x : Real}
-- given
  (J : Sym2 (Site d) -> Real)
  (hJmin : 0 < Jmin)
  (hJlo : forall e, Jmin <= J e)
  (hJhi : forall e, J e <= Jmax)
  (phase : Site d -> P)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hsurj : Function.Surjective phase)
  (hcov : PhaseCovariant J phase phaseJ)
  (hq : 1 <= q)
  (hy : 0 < y)
  (hyx : y <= x) :
-- imply
  weightedNormalizedPhaseSum d phaseJ Jmin Jmax q beta0 n y <= weightedNormalizedPhaseSum d phaseJ Jmin Jmax q beta0 n x := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedThreshold.weightedNormalizedPhaseSum_mono_beta d n J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov q beta0 y x hq hy hyx

/--
[weightedThresholdPhaseSum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedThreshold.lean)
-/
@[path]
private lemma weightedThresholdPhaseSum_nonneg_eq
  {d n : Nat}
  [Fintype P]
  {Jmin Jmax q beta0 beta : Real}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall a e, 0 < phaseJ a e)
  (hJmin : 0 < Jmin)
  (hq : 1 <= q) :
-- imply
  0 <= weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0 n beta := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedThreshold.weightedThresholdPhaseSum_nonneg d n phaseJ hJ Jmin Jmax q beta0 beta hJmin hq

/--
[weightedThresholdPhaseSum_le_card_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedThreshold.lean)
-/
@[path]
private lemma weightedThresholdPhaseSum_le_card_div_eq
  {d n : Nat}
  [Fintype P]
  {Jmin Jmax q beta0 beta : Real}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall a e, 0 < phaseJ a e)
  (hJmin : 0 < Jmin)
  (hq : 1 <= q) :
-- imply
  weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0 n beta <= (Fintype.card P : Real) / weightedPhaseSharpConstant d Jmin Jmax beta0 := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedThreshold.weightedThresholdPhaseSum_le_card_div d n phaseJ hJ Jmin Jmax q beta0 beta hJmin hq

/--
[weightedThresholdPhaseSum_mono_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedThreshold.lean)
-/
@[path]
private lemma weightedThresholdPhaseSum_mono_beta_eq
  {d n : Nat}
  [Fintype P]
  [Nonempty P]
  {Jmin Jmax : Real}
  {q beta0 a b : Real}
-- given
  (J : Sym2 (Site d) -> Real)
  (hJmin : 0 < Jmin)
  (hJlo : forall e, Jmin <= J e)
  (hJhi : forall e, J e <= Jmax)
  (phase : Site d -> P)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hsurj : Function.Surjective phase)
  (hcov : PhaseCovariant J phase phaseJ)
  (hq : 1 <= q)
  (hab : a <= b) :
-- imply
  weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0 n a <= weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0 n b := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedThreshold.weightedThresholdPhaseSum_mono_beta d n J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov q beta0 a b hq hab

/--
[weightedThresholdSig_mono_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedThreshold.lean)
-/
@[path]
private lemma weightedThresholdSig_mono_beta_eq
  {d n : Nat}
  [Fintype P]
  [Nonempty P]
  {Jmin Jmax : Real}
  {q beta0 : Real}
  {a b : Real}
-- given
  (J : Sym2 (Site d) -> Real)
  (hJmin : 0 < Jmin)
  (hJlo : forall e, Jmin <= J e)
  (hJhi : forall e, J e <= Jmax)
  (phase : Site d -> P)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hsurj : Function.Surjective phase)
  (hcov : PhaseCovariant J phase phaseJ)
  (hq : 1 <= q)
  (hab : a <= b) :
-- imply
  Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n a <= Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedThreshold.weightedThresholdSig_mono_beta d n J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov q beta0 hq hab

/--
[weightedThresholdSig_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedThreshold.lean)
-/
@[path]
private lemma weightedThresholdSig_pos_eq
  {d n : Nat}
  [Fintype P]
  [Nonempty P]
  {Jmin Jmax q beta0 beta : Real}
-- given
  (hn : 1 <= n)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall a e, 0 < phaseJ a e)
  (hJmin : 0 < Jmin)
  (hq : 1 <= q) :
-- imply
  0 < Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n beta := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedThreshold.weightedThresholdSig_pos d n hn phaseJ hJ Jmin Jmax q beta0 beta hJmin hq

/--
[weightedThresholdSig_le_linear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedThreshold.lean)
-/
@[path]
private lemma weightedThresholdSig_le_linear_eq
  {d n : Nat}
  [Fintype P]
  {Jmin Jmax q beta0 beta : Real}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall a e, 0 < phaseJ a e)
  (hJmin : 0 < Jmin)
  (hq : 1 <= q) :
-- imply
  Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n beta <= ((Fintype.card P : Real) / weightedPhaseSharpConstant d Jmin Jmax beta0) * (n : Real) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedThreshold.weightedThresholdSig_le_linear d n phaseJ hJ Jmin Jmax q beta0 beta hJmin hq

/--
[weightedThresholdSet_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedThreshold.lean)
-/
@[path]
private lemma weightedThresholdSet_nonneg_eq
  {d : Nat}
  [Fintype P]
  [Nonempty P]
  {Jmin Jmax q beta0 : Real}
  {beta : Real}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJmin : 0 < Jmin)
  (hmem : beta ∈ thresholdSet (fun b n => Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)) :
-- imply
  0 <= beta := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedThreshold.weightedThresholdSet_nonneg d phaseJ Jmin Jmax q beta0 hJmin beta hmem

/--
[weightedThresholdSet_bddBelow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedThreshold.lean)
-/
@[path]
private lemma weightedThresholdSet_bddBelow_eq
  {d : Nat}
  [Fintype P]
  [Nonempty P]
  {Jmin Jmax q beta0 : Real}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJmin : 0 < Jmin) :
-- imply
  BddBelow (thresholdSet (fun b n => Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedThreshold.weightedThresholdSet_bddBelow d phaseJ Jmin Jmax q beta0 hJmin

/--
[weightedThresholdLogRatio_bddAbove](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedThreshold.lean)
-/
@[path]
private lemma weightedThresholdLogRatio_bddAbove_eq
  {d : Nat}
  [Fintype P]
  [Nonempty P]
  {Jmin Jmax q beta0 beta : Real}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall a e, 0 < phaseJ a e)
  (hJmin : 0 < Jmin)
  (hq : 1 <= q) :
-- imply
  Filter.IsBoundedUnder (fun x y : Real => x <= y) atTop (logRatio (fun n => Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n beta)) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedThreshold.weightedThresholdLogRatio_bddAbove d phaseJ hJ Jmin Jmax q beta0 beta hJmin hq

/--
[weightedThresholdLogRatio_isCobounded](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedThreshold.lean)
-/
@[path]
private lemma weightedThresholdLogRatio_isCobounded_eq
  {d : Nat}
  [Fintype P]
  [Nonempty P]
  {Jmin Jmax q beta0 beta : Real}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall a e, 0 < phaseJ a e)
  (hJmin : 0 < Jmin)
  (hq : 1 <= q) :
-- imply
  Filter.IsCoboundedUnder (fun x y : Real => x <= y) atTop (logRatio (fun n => Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n beta)) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedThreshold.weightedThresholdLogRatio_isCobounded d phaseJ hJ Jmin Jmax q beta0 beta hJmin hq

/--
[weightedThresholdSet_mem_of_selectedPhaseSum_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedThreshold.lean)
-/
@[path]
private lemma weightedThresholdSet_mem_of_selectedPhaseSum_pos_eq
  {d : Nat}
  [Fintype P]
  [Nonempty P]
  {Jmin Jmax q beta0 beta : Real}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall a e, 0 < phaseJ a e)
  (hJmin : 0 < Jmin)
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hTheta : 0 < weightedSelectedPhaseSum d phaseJ hJ q (zero_lt_one.trans_le hq) beta) :
-- imply
  beta ∈ thresholdSet (fun b n => Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedThreshold.weightedThresholdSet_mem_of_selectedPhaseSum_pos d phaseJ hJ Jmin Jmax q beta0 beta hJmin hq hbeta hTheta

/--
[weightedThresholdSet_nonempty_of_selectedPhaseSum_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedThreshold.lean)
-/
@[path]
private lemma weightedThresholdSet_nonempty_of_selectedPhaseSum_pos_eq
  {d : Nat}
  [Fintype P]
  [Nonempty P]
  {Jmin Jmax q beta0 beta : Real}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall a e, 0 < phaseJ a e)
  (hJmin : 0 < Jmin)
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hTheta : 0 < weightedSelectedPhaseSum d phaseJ hJ q (zero_lt_one.trans_le hq) beta) :
-- imply
  (thresholdSet (fun b n => Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)).Nonempty := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedThreshold.weightedThresholdSet_nonempty_of_selectedPhaseSum_pos d phaseJ hJ Jmin Jmax q beta0 beta hJmin hq hbeta hTheta

/--
[weightedHighBetaWitness_threshold_member](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedThreshold.lean)
-/
@[path]
private lemma weightedHighBetaWitness_threshold_member_eq
  {d : Nat}
  [Fintype P]
  [Nonempty P]
  {Jmin Jmax q beta0 : Real}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall a e, 0 < phaseJ a e)
  (hJmin : 0 < Jmin)
  (hq : 1 <= q)
  (hhigh : weightedSelectedPhaseHighBetaWitness d phaseJ hJ q (zero_lt_one.trans_le hq) beta0) :
-- imply
  exists betaStar : Real, 0 < betaStar /\ betaStar < beta0 /\ betaStar ∈ thresholdSet (fun b n => Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedThreshold.weightedHighBetaWitness_threshold_member d phaseJ hJ Jmin Jmax q beta0 hJmin hq hhigh

/--
[weightedHighBetaWitness_threshold_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedThreshold.lean)
-/
@[path]
private lemma weightedHighBetaWitness_threshold_nonempty_eq
  {d : Nat}
  [Fintype P]
  [Nonempty P]
  {Jmin Jmax q beta0 : Real}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall a e, 0 < phaseJ a e)
  (hJmin : 0 < Jmin)
  (hq : 1 <= q)
  (hhigh : weightedSelectedPhaseHighBetaWitness d phaseJ hJ q (zero_lt_one.trans_le hq) beta0) :
-- imply
  (thresholdSet (fun b n => Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)).Nonempty := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedThreshold.weightedHighBetaWitness_threshold_nonempty d phaseJ hJ Jmin Jmax q beta0 hJmin hq hhigh

/--
[weightedHighBetaWitness_strict_cutoff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedThreshold.lean)
-/
@[path]
private lemma weightedHighBetaWitness_strict_cutoff_eq
  {d : Nat}
  [Fintype P]
  [Nonempty P]
  {Jmin Jmax q beta0 : Real}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall a e, 0 < phaseJ a e)
  (hJmin : 0 < Jmin)
  (hq : 1 <= q)
  (hhigh : weightedSelectedPhaseHighBetaWitness d phaseJ hJ q (zero_lt_one.trans_le hq) beta0) :
-- imply
  beta1 (fun b n => Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b) < beta0 := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedThreshold.weightedHighBetaWitness_strict_cutoff d phaseJ hJ Jmin Jmax q beta0 hJmin hq hhigh

/--
[weightedThresholdSig_of_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedThreshold.lean)
-/
@[path]
private lemma weightedThresholdSig_of_pos_eq
  {d n : Nat}
  [Fintype P]
  {Jmin Jmax q beta0 beta : Real}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hbeta : 0 < beta) :
-- imply
  Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n beta = Sig (weightedNormalizedPhaseSum d phaseJ Jmin Jmax q beta0) n beta := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedThreshold.weightedThresholdSig_of_pos d n phaseJ Jmin Jmax q beta0 beta hbeta

/--
[weightedSelectedPhaseSum_difference_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedThreshold.lean)
-/
@[path]
private lemma weightedSelectedPhaseSum_difference_lower_eq
  {d : Nat}
  [Fintype P]
  [Nonempty P]
  {Jmin Jmax : Real}
  {q beta0 beta' beta : Real}
-- given
  (J : Sym2 (Site d) -> Real)
  (hJmin : 0 < Jmin)
  (hJlo : forall e, Jmin <= J e)
  (hJhi : forall e, J e <= Jmax)
  (phase : Site d -> P)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hsurj : Function.Surjective phase)
  (hcov : PhaseCovariant J phase phaseJ)
  (hq : 1 <= q)
  (hne : (thresholdSet (fun b n => Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)).Nonempty)
  (hcrit : beta1 (fun b n => Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b) < beta')
  (hbeta : beta' <= beta)
  (hupper : beta <= beta0) :
-- imply
  beta - beta' <= weightedSelectedPhaseSum d phaseJ (hcov.phaseCoupling_pos hsurj (fun e => hJmin.trans_le (hJlo e))) q (zero_lt_one.trans_le hq) beta / weightedPhaseSharpConstant d Jmin Jmax beta0 - weightedSelectedPhaseSum d phaseJ (hcov.phaseCoupling_pos hsurj (fun e => hJmin.trans_le (hJlo e))) q (zero_lt_one.trans_le hq) beta' / weightedPhaseSharpConstant d Jmin Jmax beta0 := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedThreshold.weightedSelectedPhaseSum_difference_lower d J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov q beta0 beta' beta hq hne hcrit hbeta hupper

/--
[weightedSelectedPhaseSum_meanField_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedThreshold.lean)
-/
@[path]
private lemma weightedSelectedPhaseSum_meanField_lower_eq
  {d : Nat}
  [Fintype P]
  [Nonempty P]
  {Jmin Jmax : Real}
  {q beta0 beta : Real}
-- given
  (J : Sym2 (Site d) -> Real)
  (hJmin : 0 < Jmin)
  (hJlo : forall e, Jmin <= J e)
  (hJhi : forall e, J e <= Jmax)
  (phase : Site d -> P)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hsurj : Function.Surjective phase)
  (hcov : PhaseCovariant J phase phaseJ)
  (hq : 1 <= q)
  (hne : (thresholdSet (fun b n => Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)).Nonempty)
  (hcrit : beta1 (fun b n => Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b) < beta)
  (hupper : beta <= beta0) :
-- imply
  weightedPhaseSharpConstant d Jmin Jmax beta0 * (beta - beta1 (fun b n => Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)) <= weightedSelectedPhaseSum d phaseJ (hcov.phaseCoupling_pos hsurj (fun e => hJmin.trans_le (hJlo e))) q (zero_lt_one.trans_le hq) beta := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedThreshold.weightedSelectedPhaseSum_meanField_lower d J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov q beta0 beta hq hne hcrit hupper

/--
[weightedSelectedPhaseSum_mono_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedThreshold.lean)
-/
@[path]
private lemma weightedSelectedPhaseSum_mono_pos_eq
  {d : Nat}
  [Fintype P]
  [Nonempty P]
  {Jmin Jmax : Real}
  {q beta0 a b : Real}
-- given
  (J : Sym2 (Site d) -> Real)
  (hJmin : 0 < Jmin)
  (hJlo : forall e, Jmin <= J e)
  (hJhi : forall e, J e <= Jmax)
  (phase : Site d -> P)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hsurj : Function.Surjective phase)
  (hcov : PhaseCovariant J phase phaseJ)
  (hq : 1 <= q)
  (ha : 0 < a)
  (hab : a <= b) :
-- imply
  weightedSelectedPhaseSum d phaseJ (hcov.phaseCoupling_pos hsurj (fun e => hJmin.trans_le (hJlo e))) q (zero_lt_one.trans_le hq) a <= weightedSelectedPhaseSum d phaseJ (hcov.phaseCoupling_pos hsurj (fun e => hJmin.trans_le (hJlo e))) q (zero_lt_one.trans_le hq) b := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedThreshold.weightedSelectedPhaseSum_mono_pos d J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov q beta0 a b hq ha hab

/--
[weightedPhaseSum_subcritical_decay_of_threshold](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedThreshold.lean)
-/
@[path]
private lemma weightedPhaseSum_subcritical_decay_of_threshold_eq
  {d : Nat}
  [Fintype P]
  [Nonempty P]
  {Jmin Jmax : Real}
  {q delta beta beta0 : Real}
-- given
  (J : Sym2 (Site d) -> Real)
  (hJmin : 0 < Jmin)
  (hJlo : forall e, Jmin <= J e)
  (hJhi : forall e, J e <= Jmax)
  (phase : Site d -> P)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hsurj : Function.Surjective phase)
  (hcov : PhaseCovariant J phase phaseJ)
  (hq : 1 <= q)
  (hbeta0 : beta <= beta0)
  (hdelta : 0 < delta)
  (hleft : 0 < beta - 2 * delta)
  (hlt : beta < beta1 (fun b n => Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)) :
-- imply
  exists Q : Real, 0 < Q ∧ forall n : Nat, 1 <= n -> weightedPhaseSum d phaseJ q (beta - 2 * delta) n <= (Fintype.card P : Real) * Real.exp (-(((n : Real) / Q) * delta)) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedThreshold.weightedPhaseSum_subcritical_decay_of_threshold d J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov q delta beta beta0 hq hbeta0 hdelta hleft hlt

/--
[weightedPhasePhysical_subcritical_decay_of_threshold](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedThreshold.lean)
-/
@[path]
private lemma weightedPhasePhysical_subcritical_decay_of_threshold_eq
  {d : Nat}
  [Fintype P]
  [Nonempty P]
  {Jmin Jmax : Real}
  {q delta beta beta0 : Real}
-- given
  (J : Sym2 (Site d) -> Real)
  (hJmin : 0 < Jmin)
  (hJlo : forall e, Jmin <= J e)
  (hJhi : forall e, J e <= Jmax)
  (phase : Site d -> P)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hsurj : Function.Surjective phase)
  (hcov : PhaseCovariant J phase phaseJ)
  (hq : 1 <= q)
  (hbeta0 : beta <= beta0)
  (hdelta : 0 < delta)
  (hleft : 0 < beta - 2 * delta)
  (hlt : beta < beta1 (fun b n => Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)) :
-- imply
  exists Q : Real, 0 < Q ∧ forall a : P, forall n : Nat, 2 <= n -> ((weightedPhaseFiniteMeasure d n phaseJ a (hcov.phaseCoupling_pos hsurj (fun e => hJmin.trans_le (hJlo e)) a) q (beta - 2 * delta) (zero_lt_one.trans_le hq) hleft : ProbabilityMeasure _) : Measure _).real (boxBdryConnEvent d n) <= (Fintype.card P : Real) * Real.exp (-((((n : Real) / (3 * Q)) * delta))) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedThreshold.weightedPhasePhysical_subcritical_decay_of_threshold d J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov q delta beta beta0 hq hbeta0 hdelta hleft hlt

/--
[weightedSelectedPhaseSum_eq_zero_below_threshold](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedThreshold.lean)
-/
@[path]
private lemma weightedSelectedPhaseSum_eq_zero_below_threshold_eq
  {d : Nat}
  [Fintype P]
  [Nonempty P]
  {Jmin Jmax : Real}
  {q beta0 beta : Real}
-- given
  (J : Sym2 (Site d) -> Real)
  (hJmin : 0 < Jmin)
  (hJlo : forall e, Jmin <= J e)
  (hJhi : forall e, J e <= Jmax)
  (phase : Site d -> P)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hsurj : Function.Surjective phase)
  (hcov : PhaseCovariant J phase phaseJ)
  (hq : 1 <= q)
  (hcut : beta1 (fun b n => Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b) < beta0)
  (hbelow : beta < beta1 (fun b n => Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)) :
-- imply
  weightedSelectedPhaseSum d phaseJ (hcov.phaseCoupling_pos hsurj (fun e => hJmin.trans_le (hJlo e))) q (zero_lt_one.trans_le hq) beta = 0 := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedThreshold.weightedSelectedPhaseSum_eq_zero_below_threshold d J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov q beta0 beta hq hcut hbelow

/--
[weightedThreshold_eq_selectedPhaseCritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedThreshold.lean)
-/
@[path]
private lemma weightedThreshold_eq_selectedPhaseCritical_eq
  {d : Nat}
  [Fintype P]
  [Nonempty P]
  {Jmin Jmax : Real}
  {q beta0 : Real}
  {a : P}
-- given
  (J : Sym2 (Site d) -> Real)
  (hJmin : 0 < Jmin)
  (hJlo : forall e, Jmin <= J e)
  (hJhi : forall e, J e <= Jmax)
  (phase : Site d -> P)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hsurj : Function.Surjective phase)
  (hcov : PhaseCovariant J phase phaseJ)
  (hq : 1 <= q)
  (hne : (thresholdSet (fun b n => Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)).Nonempty)
  (hcut : beta1 (fun b n => Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b) < beta0) :
-- imply
  sSup (bcm_subcriticalSet (weightedPhaseThetaProfile d phaseJ (hcov.phaseCoupling_pos hsurj (fun e => hJmin.trans_le (hJlo e))) q (zero_lt_one.trans_le hq) a)) = beta1 (fun b n => Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedThreshold.weightedThreshold_eq_selectedPhaseCritical d J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov q beta0 hq hne hcut a

/--
[weightedThreshold_eq_selectedPhaseEnvelopeCritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedThreshold.lean)
-/
@[path]
private lemma weightedThreshold_eq_selectedPhaseEnvelopeCritical_eq
  {d : Nat}
  [Fintype P]
  [Nonempty P]
  {Jmin Jmax : Real}
  {q beta0 : Real}
-- given
  (J : Sym2 (Site d) -> Real)
  (hJmin : 0 < Jmin)
  (hJlo : forall e, Jmin <= J e)
  (hJhi : forall e, J e <= Jmax)
  (phase : Site d -> P)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hsurj : Function.Surjective phase)
  (hcov : PhaseCovariant J phase phaseJ)
  (hq : 1 <= q)
  (hne : (thresholdSet (fun b n => Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)).Nonempty)
  (hcut : beta1 (fun b n => Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b) < beta0) :
-- imply
  sSup {beta | Finset.univ.sup' Finset.univ_nonempty (fun a => weightedPhaseThetaProfile d phaseJ (hcov.phaseCoupling_pos hsurj (fun e => hJmin.trans_le (hJlo e))) q (zero_lt_one.trans_le hq) a beta) = 0} = beta1 (fun b n => Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedThreshold.weightedThreshold_eq_selectedPhaseEnvelopeCritical d J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov q beta0 hq hne hcut

/--
[weightedThreshold_eq_selectedPhaseCritical_of_highBetaWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedThreshold.lean)
-/
@[path]
private lemma weightedThreshold_eq_selectedPhaseCritical_of_highBetaWitness_eq
  {d : Nat}
  [Fintype P]
  [Nonempty P]
  {Jmin Jmax : Real}
  {q beta0 : Real}
  {a : P}
-- given
  (J : Sym2 (Site d) -> Real)
  (hJmin : 0 < Jmin)
  (hJlo : forall e, Jmin <= J e)
  (hJhi : forall e, J e <= Jmax)
  (phase : Site d -> P)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hsurj : Function.Surjective phase)
  (hcov : PhaseCovariant J phase phaseJ)
  (hq : 1 <= q)
  (hhigh : weightedSelectedPhaseHighBetaWitness d phaseJ (hcov.phaseCoupling_pos hsurj (fun e => hJmin.trans_le (hJlo e))) q (zero_lt_one.trans_le hq) beta0) :
-- imply
  sSup (bcm_subcriticalSet (weightedPhaseThetaProfile d phaseJ (hcov.phaseCoupling_pos hsurj (fun e => hJmin.trans_le (hJlo e))) q (zero_lt_one.trans_le hq) a)) = beta1 (fun b n => Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedThreshold.weightedThreshold_eq_selectedPhaseCritical_of_highBetaWitness d J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov q beta0 hq hhigh a

/--
[weightedThreshold_eq_selectedPhaseEnvelopeCritical_of_highBetaWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedThreshold.lean)
-/
@[path]
private lemma weightedThreshold_eq_selectedPhaseEnvelopeCritical_of_highBetaWitness_eq
  {d : Nat}
  [Fintype P]
  [Nonempty P]
  {Jmin Jmax : Real}
  {q beta0 : Real}
-- given
  (J : Sym2 (Site d) -> Real)
  (hJmin : 0 < Jmin)
  (hJlo : forall e, Jmin <= J e)
  (hJhi : forall e, J e <= Jmax)
  (phase : Site d -> P)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hsurj : Function.Surjective phase)
  (hcov : PhaseCovariant J phase phaseJ)
  (hq : 1 <= q)
  (hhigh : weightedSelectedPhaseHighBetaWitness d phaseJ (hcov.phaseCoupling_pos hsurj (fun e => hJmin.trans_le (hJlo e))) q (zero_lt_one.trans_le hq) beta0) :
-- imply
  sSup {beta | Finset.univ.sup' Finset.univ_nonempty (fun a => weightedPhaseThetaProfile d phaseJ (hcov.phaseCoupling_pos hsurj (fun e => hJmin.trans_le (hJlo e))) q (zero_lt_one.trans_le hq) a beta) = 0} = beta1 (fun b n => Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedThreshold.weightedThreshold_eq_selectedPhaseEnvelopeCritical_of_highBetaWitness d J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov q beta0 hq hhigh


-- created on 2026-10-23

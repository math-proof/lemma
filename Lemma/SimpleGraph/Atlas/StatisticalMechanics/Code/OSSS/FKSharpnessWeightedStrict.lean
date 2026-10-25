import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedStrict
open Finset Set StatMech StatMech.OSSS StatMech.OSSS.FKSharpnessWeightedStrict


/--
[weightedOuterInnerConn_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedStrict.lean)
-/
@[path]
private lemma weightedOuterInnerConn_nonneg_eq
  {d n : Nat}
  {q beta : Real}
  {x : Site d}
  {j : Nat}
-- given
  (J : Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < J e)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  0 <= weightedOuterInnerConn d n J q beta x j := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedStrict.weightedOuterInnerConn_nonneg d n J hJ q beta hq hbeta x j

/--
[weightedOuterInnerConn_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedStrict.lean)
-/
@[path]
private lemma weightedOuterInnerConn_le_one_eq
  {d n : Nat}
  {q beta : Real}
  {x : Site d}
  {j : Nat}
-- given
  (J : Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < J e)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  weightedOuterInnerConn d n J q beta x j <= 1 := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedStrict.weightedOuterInnerConn_le_one d n J hJ q beta hq hbeta x j

/--
[weightedOuterInnerConn_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedStrict.lean)
-/
@[path]
private lemma weightedOuterInnerConn_antitone_eq
  {d n : Nat}
  {q beta : Real}
  {x : Site d}
-- given
  (J : Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < J e)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  Antitone (weightedOuterInnerConn d n J q beta x) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedStrict.weightedOuterInnerConn_antitone d n J hJ q beta hq hbeta x

/--
[weightedOuterInnerConn_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedStrict.lean)
-/
@[path]
private lemma weightedOuterInnerConn_zero_eq
  {d n : Nat}
  {q beta : Real}
  {x : Site d}
-- given
  (J : Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < J e)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  weightedOuterInnerConn d n J q beta x 0 = 1 := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedStrict.weightedOuterInnerConn_zero d n J hJ q beta hq hbeta x

/--
[weightedPhaseProfile_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedStrict.lean)
-/
@[path]
private lemma weightedPhaseProfile_nonneg_eq
  {d : Nat}
  {a : P}
  {q beta : Real}
  {k : Nat}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall a e, 0 < phaseJ a e)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  0 <= weightedPhaseProfile d phaseJ a q beta k := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedStrict.weightedPhaseProfile_nonneg d phaseJ hJ a q beta hq hbeta k

/--
[weightedPhaseProfile_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedStrict.lean)
-/
@[path]
private lemma weightedPhaseProfile_zero_eq
  {d : Nat}
  {a : P}
  {q beta : Real}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real) :
-- imply
  weightedPhaseProfile d phaseJ a q beta 0 = 1 := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedStrict.weightedPhaseProfile_zero d phaseJ a q beta

/--
[weightedPhaseProfile_tendsto_infiniteTheta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedStrict.lean)
-/
@[path]
private lemma weightedPhaseProfile_tendsto_infiniteTheta_eq
  {d : Nat}
  {a : P}
  {q beta : Real}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < phaseJ a e)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  Filter.Tendsto (weightedPhaseProfile d phaseJ a q beta) Filter.atTop (nhds (weightedPhaseInfiniteTheta d phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta)) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedStrict.weightedPhaseProfile_tendsto_infiniteTheta d phaseJ a hJ q beta hq hbeta

/--
[weightedPhaseProfileEnvelope_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedStrict.lean)
-/
@[path]
private lemma weightedPhaseProfileEnvelope_tendsto_eq
  {d : Nat}
  [Fintype P]
  [Nonempty P]
  {q beta : Real}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall a e, 0 < phaseJ a e)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  Filter.Tendsto (phaseEnvelope (fun a => weightedPhaseProfile d phaseJ a q beta)) Filter.atTop (nhds (Finset.univ.sup' Finset.univ_nonempty (fun a => weightedPhaseInfiniteTheta d phaseJ a (hJ a) q beta (zero_lt_one.trans_le hq) hbeta))) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedStrict.weightedPhaseProfileEnvelope_tendsto d phaseJ hJ q beta hq hbeta

/--
[weightedStrictDenom_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedStrict.lean)
-/
@[path]
private lemma weightedStrictDenom_pos_eq
  {d n : Nat}
  {q beta : Real}
-- given
  (hn : 1 <= n)
  (J : Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < J e)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  0 < weightedStrictDenom d n J q beta := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedStrict.weightedStrictDenom_pos d n hn J hJ q beta hq hbeta

/--
[weightedStrictDenom_le_phaseEnvelopeSig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedStrict.lean)
-/
@[path]
private lemma weightedStrictDenom_le_phaseEnvelopeSig_eq
  {d n : Nat}
  [Fintype P]
  [Nonempty P]
  {q beta : Real}
-- given
  (J : Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < J e)
  (phase : Site d -> P)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hsurj : Function.Surjective phase)
  (hcov : PhaseCovariant J phase phaseJ)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  weightedStrictDenom d n J q beta <= 8 * weightedPhaseEnvelopeSig d n phaseJ q beta / (n : Real) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedStrict.weightedStrictDenom_le_phaseEnvelopeSig d n J hJ phase phaseJ hsurj hcov q beta hq hbeta


-- created on 2026-10-23

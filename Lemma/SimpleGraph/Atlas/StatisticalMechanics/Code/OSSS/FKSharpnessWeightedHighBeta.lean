import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedHighBeta
open Finset Set Filter Topology MeasureTheory StatMech StatMech.FK StatMech.OSSS StatMech.OSSS.FKSharpnessWeightedHighBeta


/--
[edgeProductW_cross_params](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedHighBeta.lean)
-/
@[path]
private lemma edgeProductW_cross_params_eq
  [Fintype V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf1 pf2 : Sym2 V -> Real}
  {a b : ConfigSpace (Sym2 V)}
-- given
  (hpf1 : forall e, 0 < pf1 e)
  (hpf1' : forall e, pf1 e < 1)
  (hpf2 : forall e, 0 < pf2 e)
  (hpf2' : forall e, pf2 e < 1)
  (hle : forall e, pf1 e <= pf2 e) :
-- imply
  edgeProductW G pf1 a * edgeProductW G pf2 b <= edgeProductW G pf1 (a ⊓ b) * edgeProductW G pf2 (a ⊔ b) := by
-- proof
  apply StatMech.FK.edgeProductW_cross_params G hpf1 hpf1' hpf2 hpf2' hle a b

/--
[bcWeightW_cross_params](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedHighBeta.lean)
-/
@[path]
private lemma bcWeightW_cross_params_eq
  [Fintype V]
  {G C : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableRel C.Adj]
  {pf1 pf2 : Sym2 V -> Real}
  {q : Real}
  {a b : ConfigSpace (Sym2 V)}
-- given
  (hpf1 : forall e, 0 < pf1 e)
  (hpf1' : forall e, pf1 e < 1)
  (hpf2 : forall e, 0 < pf2 e)
  (hpf2' : forall e, pf2 e < 1)
  (hle : forall e, pf1 e <= pf2 e)
  (hq : 1 <= q) :
-- imply
  bcWeightW G C pf1 q a * bcWeightW G C pf2 q b <= bcWeightW G C pf1 q (a ⊓ b) * bcWeightW G C pf2 q (a ⊔ b) := by
-- proof
  apply StatMech.FK.bcWeightW_cross_params G C hpf1 hpf1' hpf2 hpf2' hle hq a b

/--
[bcProbW_mono_params](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedHighBeta.lean)
-/
@[path]
private lemma bcProbW_mono_params_eq
  [Fintype V]
  [DecidableEq V]
  {G C : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableRel C.Adj]
  {pf1 pf2 : Sym2 V -> Real}
  {q : Real}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (hpf1 : forall e, 0 < pf1 e)
  (hpf1' : forall e, pf1 e < 1)
  (hpf2 : forall e, 0 < pf2 e)
  (hpf2' : forall e, pf2 e < 1)
  (hle : forall e, pf1 e <= pf2 e)
  (hq : 1 <= q)
  (hA : IsIncreasing A) :
-- imply
  (∑ omega, A.indicator (fun _ => (1 : Real)) omega * bcProbW G C pf1 q omega) <= ∑ omega, A.indicator (fun _ => (1 : Real)) omega * bcProbW G C pf2 q omega := by
-- proof
  apply StatMech.FK.bcProbW_mono_params G C hpf1 hpf1' hpf2 hpf2' hle hq hA

/--
[bcProbW_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedHighBeta.lean)
-/
@[path]
private lemma bcProbW_const_eq
  [Fintype V]
  [DecidableEq V]
  {G C : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableRel C.Adj]
  {p q : Real}
  {omega : ConfigSpace (Sym2 V)} :
-- imply
  bcProbW G C (fun _ => p) q omega = bcProb G C p q omega := by
-- proof
  apply StatMech.FK.bcProbW_const G C p q omega

/--
[wiredFinite_shell_le_weightedPhaseFinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedHighBeta.lean)
-/
@[path]
private lemma wiredFinite_shell_le_weightedPhaseFinite_eq
  {d k R : Nat}
  {a : P}
  {Jmin : Real}
  {q beta p : Real}
-- given
  (hkR : k <= R)
  (phaseJ : P -> Sym2 (Lattice.Site d) -> Real)
  (hJ : forall e, 0 < phaseJ a e)
  (hJlo : forall e, Jmin <= phaseJ a e)
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hpmin : p <= 1 - Real.exp (-(beta * Jmin))) :
-- imply
  (wiredFiniteMeasure d R hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real (boxBdryConnEvent d k) <= ((OSSS.FKSharpnessWeightedInfiniteVolume.weightedPhaseFiniteMeasure d R phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure (ConfigSpace (Sym2 (Lattice.Site d)))) : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real (boxBdryConnEvent d k) := by
-- proof
  apply StatMech.FK.wiredFinite_shell_le_weightedPhaseFinite d k R hkR phaseJ a hJ Jmin hJlo q beta p hq hbeta hp hp1 hpmin

/--
[fkTheta_le_weightedPhaseInfiniteTheta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedHighBeta.lean)
-/
@[path]
private lemma fkTheta_le_weightedPhaseInfiniteTheta_eq
  {d : Nat}
  {a : P}
  {Jmin : Real}
  {q beta p : Real}
-- given
  (phaseJ : P -> Sym2 (Lattice.Site d) -> Real)
  (hJ : forall e, 0 < phaseJ a e)
  (hJlo : forall e, Jmin <= phaseJ a e)
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hpmin : p <= 1 - Real.exp (-(beta * Jmin))) :
-- imply
  fkTheta d hp hp1 (zero_lt_one.trans_le hq) (q := q) <= OSSS.FKSharpnessWeightedInfiniteVolume.weightedPhaseInfiniteTheta d phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta := by
-- proof
  apply StatMech.FK.fkTheta_le_weightedPhaseInfiniteTheta d phaseJ a hJ Jmin hJlo q beta p hq hbeta hp hp1 hpmin

/--
[phaseCoupling_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedHighBeta.lean)
-/
@[path]
private lemma phaseCoupling_lower_eq
  {d : Nat}
  {J : Sym2 (Site d) -> Real}
  {phase : Site d -> P}
  {phaseJ : P -> Sym2 (Site d) -> Real}
  {Jmin : Real}
-- given
  (hcov : PhaseCovariant J phase phaseJ)
  (hsurj : Function.Surjective phase)
  (hJlo : forall e, Jmin <= J e) :
-- imply
  forall a e, Jmin <= phaseJ a e := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedHighBeta.phaseCoupling_lower hcov hsurj hJlo

/--
[exists_weightedSelectedPhaseSum_pos_of_two_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedHighBeta.lean)
-/
@[path]
private lemma exists_weightedSelectedPhaseSum_pos_of_two_le_eq
  {d : Nat}
  [Fintype P]
  [Nonempty P]
  {Jmin : Real}
  {q : Real}
-- given
  (hd : 2 <= d)
  (J : Sym2 (Site d) -> Real)
  (hJmin : 0 < Jmin)
  (hJlo : forall e, Jmin <= J e)
  (phase : Site d -> P)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hsurj : Function.Surjective phase)
  (hcov : PhaseCovariant J phase phaseJ)
  (hq : 1 <= q) :
-- imply
  exists betaStar : Real, 0 < betaStar /\ 0 < weightedSelectedPhaseSum d phaseJ (hcov.phaseCoupling_pos hsurj (fun e => hJmin.trans_le (hJlo e))) q (zero_lt_one.trans_le hq) betaStar := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedHighBeta.exists_weightedSelectedPhaseSum_pos_of_two_le d hd J Jmin hJmin hJlo phase phaseJ hsurj hcov q hq

/--
[exists_weightedSelectedPhaseHighBetaWitness_of_two_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedHighBeta.lean)
-/
@[path]
private lemma exists_weightedSelectedPhaseHighBetaWitness_of_two_le_eq
  {d : Nat}
  [Fintype P]
  [Nonempty P]
  {Jmin : Real}
  {q : Real}
-- given
  (hd : 2 <= d)
  (J : Sym2 (Site d) -> Real)
  (hJmin : 0 < Jmin)
  (hJlo : forall e, Jmin <= J e)
  (phase : Site d -> P)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hsurj : Function.Surjective phase)
  (hcov : PhaseCovariant J phase phaseJ)
  (hq : 1 <= q) :
-- imply
  exists beta0 : Real, weightedSelectedPhaseHighBetaWitness d phaseJ (hcov.phaseCoupling_pos hsurj (fun e => hJmin.trans_le (hJlo e))) q (zero_lt_one.trans_le hq) beta0 := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedHighBeta.exists_weightedSelectedPhaseHighBetaWitness_of_two_le d hd J Jmin hJmin hJlo phase phaseJ hsurj hcov q hq


-- created on 2026-10-23

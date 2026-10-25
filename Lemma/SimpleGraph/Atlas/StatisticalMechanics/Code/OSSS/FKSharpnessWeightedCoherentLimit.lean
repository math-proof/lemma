import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedCoherentLimit
open MeasureTheory Set Filter Topology StatMech StatMech.OSSS StatMech.OSSS.FKSharpnessWeightedCoherentLimit


/--
[weightedWiredActivePMF_toMeasure_toReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedCoherentLimit.lean)
-/
@[path]
private lemma weightedWiredActivePMF_toMeasure_toReal_eq
  {d n : Nat}
  {q beta : Real}
  {S : Set (ConfigSpace (boxGraph d n).edgeSet)}
-- given
  (J : Sym2 (boxVerts d n) -> Real)
  (hJ : forall e, 0 < J e)
  (hq : 0 < q)
  (hbeta : 0 < beta) :
-- imply
  ((weightedWiredActivePMF d n J hJ q beta hq hbeta).toMeasure S).toReal = ∑ omega : ConfigSpace (boxGraph d n).edgeSet, S.indicator (fun _ => (1 : Real)) omega * activeBCProb (boxGraph d n) (wiredBoxBoundaryGraph d n) (betaParams J beta) q omega := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedCoherentLimit.weightedWiredActivePMF_toMeasure_toReal d n J hJ q beta hq hbeta S

/--
[weightedPhaseFiniteMeasure_real_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedCoherentLimit.lean)
-/
@[path]
private lemma weightedPhaseFiniteMeasure_real_eq_eq
  {d n : Nat}
  {a : P}
  {q beta : Real}
  {A : Set (ConfigSpace (Sym2 (Site d)))}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < phaseJ a e)
  (hq : 0 < q)
  (hbeta : 0 < beta)
  (hA : MeasurableSet A) :
-- imply
  ((weightedPhaseFiniteMeasure d n phaseJ a hJ q beta hq hbeta : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Measure (ConfigSpace (Sym2 (Site d)))).real A = ∑ omega : ConfigSpace (boxGraph d n).edgeSet, (liftCfg (boxActiveEdge d n) ⁻¹' A).indicator (fun _ => (1 : Real)) omega * activeBCProb (boxGraph d n) (wiredBoxBoundaryGraph d n) (betaParams (phaseBoxCoupling phaseJ a n) beta) q omega := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedCoherentLimit.weightedPhaseFiniteMeasure_real_eq d n phaseJ a hJ q beta hq hbeta A hA

/--
[boxRestrict_liftActive_eq_on_inner_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedCoherentLimit.lean)
-/
@[path]
private lemma boxRestrict_liftActive_eq_on_inner_edges_eq
  {d : Nat}
  {k R : Nat}
  {rho : ConfigSpace (Sym2 (boxVerts d R))}
  {e : Sym2 (boxVerts d k)}
-- given
  (hkR : k <= R)
  (he : e ∈ (boxGraph d k).edgeFinset) :
-- imply
  boxRestrict d k (liftCfg (boxActiveEdge d R) (restrictActive (boxGraph d R) rho)) e = boxRestrictLE d hkR rho e := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedCoherentLimit.boxRestrict_liftActive_eq_on_inner_edges d hkR rho e he

/--
[openSub_boxRestrict_liftActive_eq_inner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedCoherentLimit.lean)
-/
@[path]
private lemma openSub_boxRestrict_liftActive_eq_inner_eq
  {d : Nat}
  {k R : Nat}
  {rho : ConfigSpace (Sym2 (boxVerts d R))}
-- given
  (hkR : k <= R) :
-- imply
  openSub (boxGraph d k) (boxRestrict d k (liftCfg (boxActiveEdge d R) (restrictActive (boxGraph d R) rho))) = openSub (boxGraph d k) (boxRestrictLE d hkR rho) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedCoherentLimit.openSub_boxRestrict_liftActive_eq_inner d hkR rho

/--
[liftActive_mem_boxBdryConnEvent_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedCoherentLimit.lean)
-/
@[path]
private lemma liftActive_mem_boxBdryConnEvent_iff_eq
  {d : Nat}
  {k R : Nat}
  {rho : ConfigSpace (Sym2 (boxVerts d R))}
-- given
  (hkR : k <= R) :
-- imply
  liftCfg (boxActiveEdge d R) (restrictActive (boxGraph d R) rho) ∈ boxBdryConnEvent d k ↔ rho ∈ connToBdryEventLE d hkR := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedCoherentLimit.liftActive_mem_boxBdryConnEvent_iff d hkR rho

/--
[weightedPhaseFiniteMeasure_shell_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedCoherentLimit.lean)
-/
@[path]
private lemma weightedPhaseFiniteMeasure_shell_eq_eq
  {d : Nat}
  {k R : Nat}
  {a : P}
  {q beta : Real}
-- given
  (hkR : k <= R)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < phaseJ a e)
  (hq : 0 < q)
  (hbeta : 0 < beta) :
-- imply
  ((weightedPhaseFiniteMeasure d R phaseJ a hJ q beta hq hbeta : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d k) = ∑ rho : ConfigSpace (Sym2 (boxVerts d R)), (connToBdryEventLE d hkR).indicator (fun _ => (1 : Real)) rho * bcProbW (boxGraph d R) (wiredBoxBoundaryGraph d R) (betaParams (phaseBoxCoupling phaseJ a R) beta) q rho := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedCoherentLimit.weightedPhaseFiniteMeasure_shell_eq d hkR phaseJ a hJ q beta hq hbeta

/--
[weighted_boxEvent_domain_dominated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedCoherentLimit.lean)
-/
@[path]
private lemma weighted_boxEvent_domain_dominated_eq
  {d r R : Nat}
  {beta q : Real}
  {A : Set (ConfigSpace (Sym2 (boxVerts d r)))}
-- given
  (hr : 1 <= r)
  (hrR : r < R)
  (J : Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < J e)
  (hbeta : 0 < beta)
  (hq : 1 <= q)
  (hA : IsIncreasing A) :
-- imply
  (∑ rho : ConfigSpace (Sym2 (boxVerts d R)), (ocd_innerRestrict (flc_incl (box_mono d (Nat.le_of_lt hrR))) ⁻¹' A).indicator (fun _ => (1 : Real)) rho * bcProbW (boxGraph d R) (wiredBoxBoundaryGraph d R) (betaParams (boxCoupling J R) beta) q rho) <= ∑ eta : ConfigSpace (Sym2 (boxVerts d r)), A.indicator (fun _ => (1 : Real)) eta * bcProbW (boxGraph d r) (wiredBoxBoundaryGraph d r) (betaParams (boxCoupling J r) beta) q eta := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedCoherentLimit.weighted_boxEvent_domain_dominated d r R hr hrR J hJ beta q hbeta hq hA

/--
[ocd_innerRestrict_box_comp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedCoherentLimit.lean)
-/
@[path]
private lemma ocd_innerRestrict_box_comp_eq
  {d : Nat}
  {k r R : Nat}
  {rho : ConfigSpace (Sym2 (boxVerts d R))}
-- given
  (hkr : k <= r)
  (hrR : r <= R) :
-- imply
  boxRestrictLE d hkr (ocd_innerRestrict (flc_incl (box_mono d hrR)) rho) = boxRestrictLE d (hkr.trans hrR) rho := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedCoherentLimit.ocd_innerRestrict_box_comp d hkr hrR rho

/--
[connToBdryEventLE_outer_eq_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedCoherentLimit.lean)
-/
@[path]
private lemma connToBdryEventLE_outer_eq_preimage_eq
  {d : Nat}
  {k r R : Nat}
-- given
  (hkr : k <= r)
  (hrR : r <= R) :
-- imply
  connToBdryEventLE d (hkr.trans hrR) = ocd_innerRestrict (flc_incl (box_mono d hrR)) ⁻¹' connToBdryEventLE d hkr := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedCoherentLimit.connToBdryEventLE_outer_eq_preimage d hkr hrR

/--
[weightedPhaseFiniteMeasure_shell_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedCoherentLimit.lean)
-/
@[path]
private lemma weightedPhaseFiniteMeasure_shell_mono_eq
  {d : Nat}
  {k r R : Nat}
  {a : P}
  {q beta : Real}
-- given
  (hk : 1 <= k)
  (hkr : k <= r)
  (hrR : r < R)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < phaseJ a e)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  ((weightedPhaseFiniteMeasure d R phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d k) <= ((weightedPhaseFiniteMeasure d r phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d k) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedCoherentLimit.weightedPhaseFiniteMeasure_shell_mono d hk hkr hrR phaseJ a hJ q beta hq hbeta

/--
[weightedPhaseWiredTheta_eq_finiteMeasure_double](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedCoherentLimit.lean)
-/
@[path]
private lemma weightedPhaseWiredTheta_eq_finiteMeasure_double_eq
  {d k : Nat}
  {a : P}
  {q beta : Real}
-- given
  (hk : 1 <= k)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < phaseJ a e)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  weightedPhaseWiredTheta d phaseJ a q beta k = ((weightedPhaseFiniteMeasure d (2 * k) phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d k) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedCoherentLimit.weightedPhaseWiredTheta_eq_finiteMeasure_double d k hk phaseJ a hJ q beta hq hbeta

/--
[weightedPhaseFiniteMeasure_fixedShell_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedCoherentLimit.lean)
-/
@[path]
private lemma weightedPhaseFiniteMeasure_fixedShell_tendsto_eq
  {d k : Nat}
  {a : P}
  {q beta : Real}
-- given
  (hk : 1 <= k)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < phaseJ a e)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  Tendsto (fun j => ((weightedPhaseFiniteMeasure d (k + j) phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d k)) atTop (nhds (weightedPhaseInfiniteShell d phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta k)) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedCoherentLimit.weightedPhaseFiniteMeasure_fixedShell_tendsto d k hk phaseJ a hJ q beta hq hbeta

/--
[weightedPhaseWiredTheta_succ_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedCoherentLimit.lean)
-/
@[path]
private lemma weightedPhaseWiredTheta_succ_le_eq
  {d n : Nat}
  {a : P}
  {q beta : Real}
-- given
  (hn : 1 <= n)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < phaseJ a e)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  weightedPhaseWiredTheta d phaseJ a q beta (n + 1) <= weightedPhaseWiredTheta d phaseJ a q beta n := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedCoherentLimit.weightedPhaseWiredTheta_succ_le d n hn phaseJ a hJ q beta hq hbeta

/--
[weightedPhaseWiredTheta_tendsto_infiniteTheta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedCoherentLimit.lean)
-/
@[path]
private lemma weightedPhaseWiredTheta_tendsto_infiniteTheta_eq
  {d : Nat}
  {a : P}
  {q beta : Real}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < phaseJ a e)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  Tendsto (weightedPhaseWiredTheta d phaseJ a q beta) atTop (nhds (weightedPhaseInfiniteTheta d phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta)) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedCoherentLimit.weightedPhaseWiredTheta_tendsto_infiniteTheta d phaseJ a hJ q beta hq hbeta

/--
[weightedPhaseDiagonalTailConvergence_of_one_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedCoherentLimit.lean)
-/
@[path]
private lemma weightedPhaseDiagonalTailConvergence_of_one_le_eq
  {d : Nat}
  {q : Real}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall a e, 0 < phaseJ a e)
  (hq : 1 <= q) :
-- imply
  WeightedPhaseDiagonalTailConvergence d phaseJ hJ q := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedCoherentLimit.weightedPhaseDiagonalTailConvergence_of_one_le d phaseJ hJ q hq


-- created on 2026-10-23

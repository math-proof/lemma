import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedPhaseClose
open MeasureTheory Set Filter Topology StatMech StatMech.OSSS StatMech.OSSS.FKSharpnessWeightedPhaseClose


/--
[weightedPhaseFiniteMeasure_relabel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPhaseClose.lean)
-/
@[path]
private lemma weightedPhaseFiniteMeasure_relabel_eq
  {d : Nat}
  {x y : Site d}
  {N m : Nat}
  {t : Finset (Sym2 (boxVerts d N))}
  {q beta : Real}
-- given
  (J : Sym2 (Site d) -> Real)
  (phase : Site d -> P)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hcov : PhaseCovariant J phase phaseJ)
  (hNm : N <= m)
  (ht : t ⊆ (boxGraph d N).edgeFinset)
  (hphaseJ : forall a e, 0 < phaseJ a e)
  (hq : 0 < q)
  (hbeta : 0 < beta) :
-- imply
  ((weightedPhaseFiniteMeasure d m phaseJ (phase y) (hphaseJ (phase y)) q beta hq hbeta : ProbabilityMeasure _) : Measure _).real (cdc_multiOpenEvent (t.image (edgeIncl d N))) = weightedTransBoxMass (phaseJ (phase x)) (y - x) N t q beta m hNm := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPhaseClose.weightedPhaseFiniteMeasure_relabel J phase phaseJ hcov x y N m hNm t ht hphaseJ q beta hq hbeta

/--
[weightedPhaseFiniteMeasure_eq_med](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPhaseClose.lean)
-/
@[path]
private lemma weightedPhaseFiniteMeasure_eq_med_eq
  {d : Nat}
  {d N R : Nat}
  {a : P}
  {q beta : Real}
  {t : Finset (Sym2 (boxVerts d N))}
-- given
  (hNR : N <= R)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < phaseJ a e)
  (hq : 0 < q)
  (hbeta : 0 < beta)
  (ht : t ⊆ (boxGraph d N).edgeFinset) :
-- imply
  ((weightedPhaseFiniteMeasure d R phaseJ a hJ q beta hq hbeta : ProbabilityMeasure _) : Measure _).real (cdc_multiOpenEvent (t.image (edgeIncl d N))) = med_multiMassProb (bcProbW (boxGraph d R) (boundaryCliqueGraph (boxBoundary d R)) (betaParams (phaseBoxCoupling phaseJ a R) beta) q) (t.image (innerEdgeLE d hNR)) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPhaseClose.weightedPhaseFiniteMeasure_eq_med d N R hNR phaseJ a hJ q beta hq hbeta t ht

/--
[weightedTransBoxMass_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPhaseClose.lean)
-/
@[path]
private lemma weightedTransBoxMass_lower_eq
  {d : Nat}
  {v : Site d}
  {N : Nat}
  {t : Finset (Sym2 (boxVerts d N))}
  {q beta : Real}
  {m : Nat}
-- given
  (K : Sym2 (Site d) -> Real)
  (hK : forall e, 0 < K e)
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hNm : N <= m)
  (hm : 1 <= m) :
-- imply
  med_multiMassProb (bcProbW (boxGraph d (m + flc_vrad v + 1)) (boundaryCliqueGraph (boxBoundary d (m + flc_vrad v + 1))) (betaParams (boxCoupling K (m + flc_vrad v + 1)) beta) q) ((flc_transEdges v N t m hNm).image (ocd_innerEdge (flc_incl ((flc_transBox_subset_box v m).trans (box_mono d (by omega)))))) <= weightedTransBoxMass K v N t q beta m hNm := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPhaseClose.weightedTransBoxMass_lower K hK v N t q beta hq hbeta m hNm hm

/--
[weightedTransBoxMass_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPhaseClose.lean)
-/
@[path]
private lemma weightedTransBoxMass_upper_eq
  {d : Nat}
  {v : Site d}
  {N : Nat}
  {t : Finset (Sym2 (boxVerts d N))}
  {q beta : Real}
  {m a : Nat}
  {tb : Finset (Sym2 (boxVerts d a))}
-- given
  (K : Sym2 (Site d) -> Real)
  (hK : forall e, 0 < K e)
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hNm : N <= m)
  (ha : 1 <= a)
  (hcond : a + flc_vrad v + 1 <= m)
  (htb : tb.image (edgeIncl d a) = (t.image (edgeIncl d N)).image (fun e => (Multiplicative.ofAdd v) • e)) :
-- imply
  weightedTransBoxMass K v N t q beta m hNm <= med_multiMassProb (bcProbW (boxGraph d a) (boundaryCliqueGraph (boxBoundary d a)) (betaParams (boxCoupling K a) beta) q) tb := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPhaseClose.weightedTransBoxMass_upper K hK v N t q beta hq hbeta m a hNm ha hcond tb htb

/--
[translateAmbientEdge_mem_lattice_edgeSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPhaseClose.lean)
-/
@[path]
private lemma translateAmbientEdge_mem_lattice_edgeSet_eq
  {d : Nat}
  {v : Site d}
  {e : Sym2 (Site d)}
-- given
  (he : e ∈ (hypercubicLattice d).edgeSet) :
-- imply
  translateAmbientEdge v e ∈ (hypercubicLattice d).edgeSet := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPhaseClose.translateAmbientEdge_mem_lattice_edgeSet v e he

/--
[ofAdd_smul_edge_eq_translateAmbientEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPhaseClose.lean)
-/
@[path]
private lemma ofAdd_smul_edge_eq_translateAmbientEdge_eq
  {d : Nat}
  {v : Site d}
  {e : Sym2 (Site d)} :
-- imply
  (Multiplicative.ofAdd v) • e = translateAmbientEdge v e := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPhaseClose.ofAdd_smul_edge_eq_translateAmbientEdge v e

/--
[weightedTransBoxMass_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPhaseClose.lean)
-/
@[path]
private lemma weightedTransBoxMass_tendsto_eq
  {d : Nat}
  {a : P}
  {v : Site d}
  {N N' M : Nat}
  {t : Finset (Sym2 (boxVerts d N))}
  {tb : Finset (Sym2 (boxVerts d N'))}
  {q beta : Real}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < phaseJ a e)
  (htb : tb ⊆ (boxGraph d N').edgeFinset)
  (hrep : tb.image (edgeIncl d N') = (t.image (edgeIncl d N)).image (fun e => (Multiplicative.ofAdd v) • e))
  (hN' : 1 <= N')
  (hNM : N <= M)
  (hbuf : N' + flc_vrad v + 1 <= M)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  Tendsto (fun k => weightedTransBoxMass (phaseJ a) v N t q beta (M + k) (hNM.trans (Nat.le_add_right M k))) atTop (nhds (((weightedPhaseInfiniteVolume d phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure _) : Measure _).real (cdc_multiOpenEvent (tb.image (edgeIncl d N'))))) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPhaseClose.weightedTransBoxMass_tendsto phaseJ a hJ v N N' M t tb htb hrep hN' hNM hbuf q beta hq hbeta

/--
[covariantWeightedSelectedPhaseTranslation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPhaseClose.lean)
-/
@[path]
private lemma covariantWeightedSelectedPhaseTranslation_eq
  {d : Nat}
  {q : Real}
-- given
  (J : Sym2 (Site d) -> Real)
  (phase : Site d -> P)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < J e)
  (hsurj : Function.Surjective phase)
  (hcov : PhaseCovariant J phase phaseJ)
  (hq : 1 <= q) :
-- imply
  CovariantWeightedSelectedPhaseTranslation d phaseJ (hcov.phaseCoupling_pos hsurj hJ) phase q (zero_lt_one.trans_le hq) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPhaseClose.covariantWeightedSelectedPhaseTranslation J phase phaseJ hJ hsurj hcov q hq

/--
[covariantWeightedSelectedPhaseLaws](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPhaseClose.lean)
-/
@[path]
private lemma covariantWeightedSelectedPhaseLaws_eq
  {d : Nat}
  {q : Real}
-- given
  (J : Sym2 (Site d) -> Real)
  (phase : Site d -> P)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < J e)
  (hsurj : Function.Surjective phase)
  (hcov : PhaseCovariant J phase phaseJ)
  (hq : 1 <= q) :
-- imply
  CovariantWeightedSelectedPhaseLaws d phaseJ (hcov.phaseCoupling_pos hsurj hJ) phase q (zero_lt_one.trans_le hq) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPhaseClose.covariantWeightedSelectedPhaseLaws J phase phaseJ hJ hsurj hcov q hq

/--
[covariantWeightedPhasePositivityTransport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPhaseClose.lean)
-/
@[path]
private lemma covariantWeightedPhasePositivityTransport_eq
  {d : Nat}
  {q : Real}
-- given
  (J : Sym2 (Site d) -> Real)
  (phase : Site d -> P)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < J e)
  (hsurj : Function.Surjective phase)
  (hcov : PhaseCovariant J phase phaseJ)
  (hq : 1 <= q) :
-- imply
  CovariantWeightedPhasePositivityTransport d J phase phaseJ hJ hsurj hcov q (zero_lt_one.trans_le hq) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPhaseClose.covariantWeightedPhasePositivityTransport J phase phaseJ hJ hsurj hcov q hq

/--
[covariant_weighted_phase_common_critical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPhaseClose.lean)
-/
@[path]
private lemma covariant_weighted_phase_common_critical_eq
  {d : Nat}
  [Fintype P]
  [Nonempty P]
  {q : Real}
  {a : P}
-- given
  (J : Sym2 (Site d) -> Real)
  (phase : Site d -> P)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < J e)
  (hsurj : Function.Surjective phase)
  (hcov : PhaseCovariant J phase phaseJ)
  (hq : 1 <= q) :
-- imply
  sSup {beta | Finset.univ.sup' Finset.univ_nonempty (fun b => weightedPhaseThetaProfile d phaseJ (hcov.phaseCoupling_pos hsurj hJ) q (zero_lt_one.trans_le hq) b beta) = 0} = sSup {beta | weightedPhaseThetaProfile d phaseJ (hcov.phaseCoupling_pos hsurj hJ) q (zero_lt_one.trans_le hq) a beta = 0} := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPhaseClose.covariant_weighted_phase_common_critical J phase phaseJ hJ hsurj hcov q hq a


-- created on 2026-10-23

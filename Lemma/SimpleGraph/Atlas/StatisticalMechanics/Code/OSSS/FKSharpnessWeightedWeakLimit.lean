import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedWeakLimit
open MeasureTheory Set Filter Topology StatMech StatMech.OSSS StatMech.OSSS.FKSharpnessWeightedWeakLimit


/--
[cdc_multiOpenEvent_isClopen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedWeakLimit.lean)
-/
@[path]
private lemma cdc_multiOpenEvent_isClopen_eq
  {d : Nat}
  {s : Finset (Sym2 (Site d))} :
-- imply
  IsClopen (cdc_multiOpenEvent s) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedWeakLimit.cdc_multiOpenEvent_isClopen s

/--
[edgeIncl_mem_lattice_edgeSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedWeakLimit.lean)
-/
@[path]
private lemma edgeIncl_mem_lattice_edgeSet_eq
  {d : Nat}
  {N : Nat}
  {e : Sym2 (boxVerts d N)}
-- given
  (he : e ∈ (boxGraph d N).edgeFinset) :
-- imply
  edgeIncl d N e ∈ (hypercubicLattice d).edgeSet := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedWeakLimit.edgeIncl_mem_lattice_edgeSet N e he

/--
[box_edges_of_image_lattice_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedWeakLimit.lean)
-/
@[path]
private lemma box_edges_of_image_lattice_edges_eq
  {d : Nat}
  {N : Nat}
  {t : Finset (Sym2 (boxVerts d N))}
-- given
  (ht : forall e, e ∈ t.image (edgeIncl d N) -> e ∈ (hypercubicLattice d).edgeSet) :
-- imply
  t ⊆ (boxGraph d N).edgeFinset := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedWeakLimit.box_edges_of_image_lattice_edges N t ht

/--
[liftActive_mem_multiOpen_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedWeakLimit.lean)
-/
@[path]
private lemma liftActive_mem_multiOpen_iff_eq
  {d : Nat}
  {d N R : Nat}
  {t : Finset (Sym2 (boxVerts d N))}
  {rho : ConfigSpace (Sym2 (boxVerts d R))}
-- given
  (hNR : N <= R)
  (ht : t ⊆ (boxGraph d N).edgeFinset) :
-- imply
  liftCfg (boxActiveEdge d R) (restrictActive (boxGraph d R) rho) ∈ cdc_multiOpenEvent (t.image (edgeIncl d N)) <-> ocd_innerRestrict (flc_incl (box_mono d hNR)) rho ∈ cdc_boxMultiOpenEvent N t := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedWeakLimit.liftActive_mem_multiOpen_iff d N R hNR t ht rho

/--
[weightedPhaseFiniteMeasure_multiOpen_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedWeakLimit.lean)
-/
@[path]
private lemma weightedPhaseFiniteMeasure_multiOpen_eq_eq
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
  ((weightedPhaseFiniteMeasure d R phaseJ a hJ q beta hq hbeta : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent (t.image (edgeIncl d N))) = ∑ rho : ConfigSpace (Sym2 (boxVerts d R)), (ocd_innerRestrict (flc_incl (box_mono d hNR)) ⁻¹' cdc_boxMultiOpenEvent N t).indicator (fun _ => (1 : Real)) rho * bcProbW (boxGraph d R) (wiredBoxBoundaryGraph d R) (betaParams (phaseBoxCoupling phaseJ a R) beta) q rho := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedWeakLimit.weightedPhaseFiniteMeasure_multiOpen_eq d N R hNR phaseJ a hJ q beta hq hbeta t ht

/--
[weightedPhaseFiniteMeasure_multiOpen_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedWeakLimit.lean)
-/
@[path]
private lemma weightedPhaseFiniteMeasure_multiOpen_mono_eq
  {d : Nat}
  {d N r R : Nat}
  {a : P}
  {q beta : Real}
  {t : Finset (Sym2 (boxVerts d N))}
-- given
  (hN : 1 <= N)
  (hNr : N <= r)
  (hrR : r < R)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < phaseJ a e)
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (ht : t ⊆ (boxGraph d N).edgeFinset) :
-- imply
  ((weightedPhaseFiniteMeasure d R phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure _) : Measure _).real (cdc_multiOpenEvent (t.image (edgeIncl d N))) <= ((weightedPhaseFiniteMeasure d r phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure _) : Measure _).real (cdc_multiOpenEvent (t.image (edgeIncl d N))) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedWeakLimit.weightedPhaseFiniteMeasure_multiOpen_mono d N r R hN hNr hrR phaseJ a hJ q beta hq hbeta t ht

/--
[weightedPhaseFiniteMeasure_multiOpen_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedWeakLimit.lean)
-/
@[path]
private lemma weightedPhaseFiniteMeasure_multiOpen_tendsto_eq
  {d : Nat}
  {d N : Nat}
  {a : P}
  {q beta : Real}
  {t : Finset (Sym2 (boxVerts d N))}
-- given
  (hN : 1 <= N)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < phaseJ a e)
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (ht : t ⊆ (boxGraph d N).edgeFinset) :
-- imply
  Tendsto (fun R => ((weightedPhaseFiniteMeasure d R phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure _) : Measure _).real (cdc_multiOpenEvent (t.image (edgeIncl d N)))) atTop (nhds (((weightedPhaseInfiniteVolume d phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure _) : Measure _).real (cdc_multiOpenEvent (t.image (edgeIncl d N))))) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedWeakLimit.weightedPhaseFiniteMeasure_multiOpen_tendsto d N hN phaseJ a hJ q beta hq hbeta t ht

/--
[weightedPhaseFiniteMeasure_nonLattice_multiOpen_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedWeakLimit.lean)
-/
@[path]
private lemma weightedPhaseFiniteMeasure_nonLattice_multiOpen_zero_eq
  {d : Nat}
  {d n : Nat}
  {a : P}
  {q beta : Real}
  {T : Finset (Sym2 (Site d))}
  {e : Sym2 (Site d)}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < phaseJ a e)
  (hq : 0 < q)
  (hbeta : 0 < beta)
  (heT : e ∈ T)
  (he : e ∉ (hypercubicLattice d).edgeSet) :
-- imply
  ((weightedPhaseFiniteMeasure d n phaseJ a hJ q beta hq hbeta : ProbabilityMeasure _) : Measure _).real (cdc_multiOpenEvent T) = 0 := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedWeakLimit.weightedPhaseFiniteMeasure_nonLattice_multiOpen_zero d n phaseJ a hJ q beta hq hbeta T e heT he

/--
[weightedPhaseInfiniteVolume_nonLattice_multiOpen_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedWeakLimit.lean)
-/
@[path]
private lemma weightedPhaseInfiniteVolume_nonLattice_multiOpen_zero_eq
  {d : Nat}
  {d : Nat}
  {a : P}
  {q beta : Real}
  {T : Finset (Sym2 (Site d))}
  {e : Sym2 (Site d)}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < phaseJ a e)
  (hq : 0 < q)
  (hbeta : 0 < beta)
  (heT : e ∈ T)
  (he : e ∉ (hypercubicLattice d).edgeSet) :
-- imply
  ((weightedPhaseInfiniteVolume d phaseJ a hJ q beta hq hbeta : ProbabilityMeasure _) : Measure _).real (cdc_multiOpenEvent T) = 0 := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedWeakLimit.weightedPhaseInfiniteVolume_nonLattice_multiOpen_zero d phaseJ a hJ q beta hq hbeta T e heT he

/--
[lattice_finset_in_positive_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedWeakLimit.lean)
-/
@[path]
private lemma lattice_finset_in_positive_box_eq
  {d : Nat}
  {T : Finset (Sym2 (Site d))}
-- given
  (hT : forall e, e ∈ T -> e ∈ (hypercubicLattice d).edgeSet) :
-- imply
  exists N : Nat, 1 <= N ∧ exists t : Finset (Sym2 (boxVerts d N)), t ⊆ (boxGraph d N).edgeFinset ∧ T = t.image (edgeIncl d N) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedWeakLimit.lattice_finset_in_positive_box T hT

/--
[weightedPhaseFiniteMeasure_tendsto_selected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedWeakLimit.lean)
-/
@[path]
private lemma weightedPhaseFiniteMeasure_tendsto_selected_eq
  {d : Nat}
  {d : Nat}
  {a : P}
  {q beta : Real}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < phaseJ a e)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  WeakConvergesTo (fun n => weightedPhaseFiniteMeasure d n phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta) (weightedPhaseInfiniteVolume d phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedWeakLimit.weightedPhaseFiniteMeasure_tendsto_selected d phaseJ a hJ q beta hq hbeta

/--
[weightedPhaseFiniteMeasure_weakLimit_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedWeakLimit.lean)
-/
@[path]
private lemma weightedPhaseFiniteMeasure_weakLimit_unique_eq
  {d : Nat}
  {d : Nat}
  {a : P}
  {q beta : Real}
  {mu : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < phaseJ a e)
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hmu : WeakConvergesTo (fun n => weightedPhaseFiniteMeasure d n phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta) mu) :
-- imply
  mu = weightedPhaseInfiniteVolume d phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedWeakLimit.weightedPhaseFiniteMeasure_weakLimit_unique d phaseJ a hJ q beta hq hbeta mu hmu


-- created on 2026-10-23

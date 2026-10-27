import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedSelectedLaws.Part3
open MeasureTheory Set Filter Topology StatMech StatMech.OSSS StatMech.OSSS.FKSharpnessWeightedSelectedLaws


/--
[weightedOpenTolerance_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedSelectedLaws.lean)
-/
@[path]
private lemma weightedOpenTolerance_pos_eq
  {d : Nat}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q) :
-- imply
  0 < weightedOpenTolerance p q := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedSelectedLaws.weightedOpenTolerance_pos hp hp1 hq

/--
[activeBCProb_singleOpen_preimage_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedSelectedLaws.lean)
-/
@[path]
private lemma activeBCProb_singleOpen_preimage_bound_eq
  {d : Nat}
  [Fintype V]
  [DecidableEq V]
  {G C : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableRel C.Adj]
  {pf : Sym2 V -> Real}
  {q : Real}
  {e : G.edgeSet}
  {A : Set (ConfigSpace G.edgeSet)}
-- given
  (hpf : forall e, 0 < pf e)
  (hpf1 : forall e, pf e < 1)
  (hq : 1 <= q) :
-- imply
  weightedOpenTolerance (pf e.1) q * (∑ omega, (setOpen e ⁻¹' A).indicator (fun _ => (1 : Real)) omega * activeBCProb G C pf q omega) <= ∑ omega, A.indicator (fun _ => (1 : Real)) omega * activeBCProb G C pf q omega := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedSelectedLaws.activeBCProb_singleOpen_preimage_bound G C hpf hpf1 hq e A

/--
[liftCfg_setOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedSelectedLaws.lean)
-/
@[path]
private lemma liftCfg_setOpen_eq
  {d : Nat}
  [Fintype E]
  [DecidableEq E]
  {e : E}
  {omega : ConfigSpace E}
-- given
  (edge : E -> Sym2 (Site d))
  (hinj : Function.Injective edge) :
-- imply
  liftCfg edge (setOpen e omega) = setOpen (edge e) (liftCfg edge omega) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedSelectedLaws.liftCfg_setOpen edge hinj e omega

/--
[weightedPhaseFiniteMeasure_singleOpen_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedSelectedLaws.lean)
-/
@[path]
private lemma weightedPhaseFiniteMeasure_singleOpen_bound_eq
  {d : Nat}
  {d n : Nat}
  {a : P}
  {q beta : Real}
  {e : (boxGraph d n).edgeSet}
  {A : Set (ConfigSpace (Sym2 (Site d)))}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < phaseJ a e)
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hA : MeasurableSet A) :
-- imply
  weightedOpenTolerance (betaParams (phaseJ a) beta (boxActiveEdge d n e)) q * ((weightedPhaseFiniteMeasure d n phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Measure _).real (setOpen (boxActiveEdge d n e) ⁻¹' A) <= ((weightedPhaseFiniteMeasure d n phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Measure _).real A := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedSelectedLaws.weightedPhaseFiniteMeasure_singleOpen_bound d n phaseJ a hJ q beta hq hbeta e A hA

/--
[weightedPhaseInfinite_singleOpen_cylinder_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedSelectedLaws.lean)
-/
@[path]
private lemma weightedPhaseInfinite_singleOpen_cylinder_bound_eq
  {d : Nat}
  {d N : Nat}
  {a : P}
  {q beta : Real}
  {eb : Sym2 (boxVerts d N)}
  {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < phaseJ a e)
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (heb : eb ∈ (boxGraph d N).edgeFinset) :
-- imply
  weightedOpenTolerance (betaParams (phaseJ a) beta (edgeIncl d N eb)) q * ((weightedPhaseInfiniteVolume d phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Measure _).real (boxRestrict d N ⁻¹' (setOpen eb ⁻¹' S)) <= ((weightedPhaseInfiniteVolume d phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Measure _).real (boxRestrict d N ⁻¹' S) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedSelectedLaws.weightedPhaseInfinite_singleOpen_cylinder_bound d N phaseJ a hJ q beta hq hbeta eb heb S

/--
[weightedPhaseInfinite_singleOpen_fullCylinder_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedSelectedLaws.lean)
-/
@[path]
private lemma weightedPhaseInfinite_singleOpen_fullCylinder_bound_eq
  {d : Nat}
  {d N : Nat}
  {a : P}
  {q beta : Real}
  {eN : (boxGraph d N).edgeSet}
  {C : Set (ConfigSpace (Sym2 (Site d)))}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < phaseJ a e)
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hC : C ∈ measurableCylinders (fun _ : Sym2 (Site d) => Bool)) :
-- imply
  weightedOpenTolerance (betaParams (phaseJ a) beta (boxActiveEdge d N eN)) q * ((weightedPhaseInfiniteVolume d phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Measure _).real (setOpen (boxActiveEdge d N eN) ⁻¹' C) <= ((weightedPhaseInfiniteVolume d phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Measure _).real C := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedSelectedLaws.weightedPhaseInfinite_singleOpen_fullCylinder_bound d N phaseJ a hJ q beta hq hbeta eN C hC

/--
[weightedPhaseInfinite_setOpen_absolutelyContinuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedSelectedLaws.lean)
-/
@[path]
private lemma weightedPhaseInfinite_setOpen_absolutelyContinuous_eq
  {d : Nat}
  {d N : Nat}
  {a : P}
  {q beta : Real}
  {eN : (boxGraph d N).edgeSet}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < phaseJ a e)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  ((weightedPhaseInfiniteVolume d phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Measure _).map (setOpen (boxActiveEdge d N eN)) ≪ ((weightedPhaseInfiniteVolume d phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Measure _) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedSelectedLaws.weightedPhaseInfinite_setOpen_absolutelyContinuous d N phaseJ a hJ q beta hq hbeta eN

/--
[weightedPhaseInfinite_hasBoxFiniteEnergy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedSelectedLaws.lean)
-/
@[path]
private lemma weightedPhaseInfinite_hasBoxFiniteEnergy_eq
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
  HasBoxFiniteEnergy (weightedPhaseInfiniteVolume d phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedSelectedLaws.weightedPhaseInfinite_hasBoxFiniteEnergy d phaseJ a hJ q beta hq hbeta

/--
[weightedSelectedPhaseFiniteEnergy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedSelectedLaws.lean)
-/
@[path]
private lemma weightedSelectedPhaseFiniteEnergy_eq
  {d : Nat}
  {d : Nat}
  {q : Real}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall a e, 0 < phaseJ a e)
  (hq : 1 <= q) :
-- imply
  WeightedSelectedPhaseFiniteEnergy d phaseJ hJ q (zero_lt_one.trans_le hq) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedSelectedLaws.weightedSelectedPhaseFiniteEnergy d phaseJ hJ q hq

/--
[coherentTranslatedLaw_covariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedSelectedLaws.lean)
-/
@[path]
private lemma coherentTranslatedLaw_covariant_eq
  {d : Nat}
  {mu : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))}
  {x y : Site d} :
-- imply
  (coherentTranslatedLaw mu y : Measure (ConfigSpace (Sym2 (Site d)))) = (coherentTranslatedLaw mu x : Measure (ConfigSpace (Sym2 (Site d)))).map (ConfigSpace.shift (Multiplicative.ofAdd (x - y))) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedSelectedLaws.coherentTranslatedLaw_covariant mu x y


-- created on 2026-10-23

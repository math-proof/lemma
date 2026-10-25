import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusFacePrimitive.Part2
open StatMech StatMech.FrontierA


/--
[triangularTorusEvenHomology_eq_zero_of_surfaceHomology](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePrimitive.lean)
-/
@[path]
private lemma triangularTorusEvenHomology_eq_zero_of_surfaceHomology_eq
  {L : Nat}
  [Fact (2 < L)]
  {F : Finset (Sym2 (ZMod L × ZMod L))}
-- given
  (hhom : surfaceSubgraphHomology (triangularTorusSurfaceEdgeClass L) F = 0) :
-- imply
  triangularTorusEvenHomology L F = 0 := by
-- proof
  apply StatMech.FrontierA.triangularTorusEvenHomology_eq_zero_of_surfaceHomology L F hhom

/--
[triangularTorus_dartEdge_mem_cycle_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePrimitive.lean)
-/
@[path]
private lemma triangularTorus_dartEdge_mem_cycle_iff_eq
  {L : Nat}
  [Fact (2 < L)]
  {root : ZMod L × ZMod L}
  {p : (triangularTorusGraph L).Walk root root}
-- given
  (hp : p.IsCycle) :
-- imply
  letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ forall (k : Fin p.darts.length) (a : Fin 6), (triangularTorusDartEquiv L ((triangularTorusCycleNativeDart L p k).1, a)).edge ∈ p.edges.toFinset ↔ ((triangularTorusCycleNativeDart L p k).1, a) = triangularTorusCycleNativeDart L p k ∨ ((triangularTorusCycleNativeDart L p k).1, a) = triangularTorusDartReverse L (triangularTorusCycleNativeDart L p (k - 1)) := by
-- proof
  apply StatMech.FrontierA.triangularTorus_dartEdge_mem_cycle_iff L p hp

/--
[triangularZeroHomology_boundaryCoeff_cast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePrimitive.lean)
-/
@[path]
private lemma triangularZeroHomology_boundaryCoeff_cast_eq
  {L : Nat}
  [Fact (2 < L)]
  {F : Finset (Sym2 (ZMod L × ZMod L))}
  {d : triangularTorusDart L}
-- given
  (hF : F ∈ StatMech.Ising.evenSubgraphs (triangularTorusGraph L))
  (hhom : triangularTorusEvenHomology L F = 0) :
-- imply
  (triangularFaceBoundaryCoeff (triangularZeroHomologyLowerPotential L F) (triangularZeroHomologyUpperPotential L F) d : ZMod 2) = (ons_edgeBit F (triangularTorusDartEquiv L d).edge : ZMod 2) := by
-- proof
  apply StatMech.FrontierA.triangularZeroHomology_boundaryCoeff_cast L F hF hhom d

/--
[triangularZeroHomology_boundaryCoeff_eq_zero_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePrimitive.lean)
-/
@[path]
private lemma triangularZeroHomology_boundaryCoeff_eq_zero_of_not_mem_eq
  {L : Nat}
  [Fact (2 < L)]
  {F : Finset (Sym2 (ZMod L × ZMod L))}
  {d : triangularTorusDart L}
-- given
  (hF : F ∈ StatMech.Ising.evenSubgraphs (triangularTorusGraph L))
  (hhom : triangularTorusEvenHomology L F = 0)
  (hnot : (triangularTorusDartEquiv L d).edge ∉ F) :
-- imply
  triangularFaceBoundaryCoeff (triangularZeroHomologyLowerPotential L F) (triangularZeroHomologyUpperPotential L F) d = 0 := by
-- proof
  apply StatMech.FrontierA.triangularZeroHomology_boundaryCoeff_eq_zero_of_not_mem L F hF hhom d hnot

/--
[triangularZeroHomology_boundaryCoeff_ne_zero_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePrimitive.lean)
-/
@[path]
private lemma triangularZeroHomology_boundaryCoeff_ne_zero_of_mem_eq
  {L : Nat}
  [Fact (2 < L)]
  {F : Finset (Sym2 (ZMod L × ZMod L))}
  {d : triangularTorusDart L}
-- given
  (hF : F ∈ StatMech.Ising.evenSubgraphs (triangularTorusGraph L))
  (hhom : triangularTorusEvenHomology L F = 0)
  (hmem : (triangularTorusDartEquiv L d).edge ∈ F) :
-- imply
  triangularFaceBoundaryCoeff (triangularZeroHomologyLowerPotential L F) (triangularZeroHomologyUpperPotential L F) d ≠ 0 := by
-- proof
  apply StatMech.FrontierA.triangularZeroHomology_boundaryCoeff_ne_zero_of_mem L F hF hhom d hmem

/--
[triangularZeroHomology_cycleBoundaryCoeff_eq_prev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePrimitive.lean)
-/
@[path]
private lemma triangularZeroHomology_cycleBoundaryCoeff_eq_prev_eq
  {L : Nat}
  [Fact (2 < L)]
  {root : ZMod L × ZMod L}
  {p : (triangularTorusGraph L).Walk root root}
-- given
  (hp : p.IsCycle)
  (hhom : triangularTorusEvenHomology L p.edges.toFinset = 0) :
-- imply
  letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ forall k : Fin p.darts.length, triangularFaceBoundaryCoeff (triangularZeroHomologyLowerPotential L p.edges.toFinset) (triangularZeroHomologyUpperPotential L p.edges.toFinset) (triangularTorusCycleNativeDart L p k) = triangularFaceBoundaryCoeff (triangularZeroHomologyLowerPotential L p.edges.toFinset) (triangularZeroHomologyUpperPotential L p.edges.toFinset) (triangularTorusCycleNativeDart L p (k - 1)) := by
-- proof
  apply StatMech.FrontierA.triangularZeroHomology_cycleBoundaryCoeff_eq_prev L p hp hhom

/--
[triangularZeroHomology_cycleBoundaryCoeff_eq_root](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePrimitive.lean)
-/
@[path]
private lemma triangularZeroHomology_cycleBoundaryCoeff_eq_root_eq
  {L : Nat}
  [Fact (2 < L)]
  {root : ZMod L × ZMod L}
  {p : (triangularTorusGraph L).Walk root root}
-- given
  (hp : p.IsCycle)
  (hhom : triangularTorusEvenHomology L p.edges.toFinset = 0) :
-- imply
  letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ forall k : Fin p.darts.length, triangularFaceBoundaryCoeff (triangularZeroHomologyLowerPotential L p.edges.toFinset) (triangularZeroHomologyUpperPotential L p.edges.toFinset) (triangularTorusCycleNativeDart L p k) = triangularFaceBoundaryCoeff (triangularZeroHomologyLowerPotential L p.edges.toFinset) (triangularZeroHomologyUpperPotential L p.edges.toFinset) (triangularTorusCycleNativeDart L p 0) := by
-- proof
  apply StatMech.FrontierA.triangularZeroHomology_cycleBoundaryCoeff_eq_root L p hp hhom

/--
[triangularZeroHomology_cycleBoundaryCoeff_root_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePrimitive.lean)
-/
@[path]
private lemma triangularZeroHomology_cycleBoundaryCoeff_root_ne_zero_eq
  {L : Nat}
  [Fact (2 < L)]
  {root : ZMod L × ZMod L}
  {p : (triangularTorusGraph L).Walk root root}
-- given
  (hp : p.IsCycle)
  (hhom : triangularTorusEvenHomology L p.edges.toFinset = 0) :
-- imply
  letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ triangularFaceBoundaryCoeff (triangularZeroHomologyLowerPotential L p.edges.toFinset) (triangularZeroHomologyUpperPotential L p.edges.toFinset) (triangularTorusCycleNativeDart L p 0) ≠ 0 := by
-- proof
  apply StatMech.FrontierA.triangularZeroHomology_cycleBoundaryCoeff_root_ne_zero L p hp hhom

/--
[triangularPositiveEdge_index_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePrimitive.lean)
-/
@[path]
private lemma triangularPositiveEdge_index_source_eq
  {L : Nat}
  [Fact (2 < L)]
  {d : triangularTorusDart L} :
-- imply
  triangularPositiveEdge L (triangularTorusPositiveIndex d.2) (triangularTorusPositiveSource d) = (triangularTorusDartEquiv L d).edge := by
-- proof
  apply StatMech.FrontierA.triangularPositiveEdge_index_source L d

/--
[triangularTorusCycle_positiveRepresentation_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePrimitive.lean)
-/
@[path]
private lemma triangularTorusCycle_positiveRepresentation_injective_eq
  {L : Nat}
  [Fact (2 < L)]
  {root : ZMod L × ZMod L}
  {p : (triangularTorusGraph L).Walk root root}
-- given
  (hp : p.IsCycle) :
-- imply
  Function.Injective (fun k : Fin p.darts.length => triangularTorusPositiveRepresentation (triangularTorusCycleNativeDart L p k)) := by
-- proof
  apply StatMech.FrontierA.triangularTorusCycle_positiveRepresentation_injective L p hp

/--
[triangularBoundaryCoeff_mul_step_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePrimitive.lean)
-/
@[path]
private lemma triangularBoundaryCoeff_mul_step_fst_eq
  {L : Nat}
  {lower upper : (ZMod L × ZMod L) → ZMod 2}
  {d : triangularTorusDart L} :
-- imply
  triangularFaceBoundaryCoeff lower upper d * (triangularIntStep d.2).1 = triangularFacePositiveCoeff lower upper (triangularTorusPositiveIndex d.2) (triangularTorusPositiveSource d) * (triangularIntStep (triangularTorusPositiveDirection (triangularTorusPositiveIndex d.2))).1 := by
-- proof
  apply StatMech.FrontierA.triangularBoundaryCoeff_mul_step_fst lower upper d

/--
[triangularBoundaryCoeff_mul_step_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePrimitive.lean)
-/
@[path]
private lemma triangularBoundaryCoeff_mul_step_snd_eq
  {L : Nat}
  {lower upper : (ZMod L × ZMod L) → ZMod 2}
  {d : triangularTorusDart L} :
-- imply
  triangularFaceBoundaryCoeff lower upper d * (triangularIntStep d.2).2 = triangularFacePositiveCoeff lower upper (triangularTorusPositiveIndex d.2) (triangularTorusPositiveSource d) * (triangularIntStep (triangularTorusPositiveDirection (triangularTorusPositiveIndex d.2))).2 := by
-- proof
  apply StatMech.FrontierA.triangularBoundaryCoeff_mul_step_snd lower upper d

/--
[triangularFacePositiveCoeff_full_fst_sum_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePrimitive.lean)
-/
@[path]
private lemma triangularFacePositiveCoeff_full_fst_sum_eq_zero_eq
  {L : Nat}
  [NeZero L]
  {lower upper : (ZMod L × ZMod L) → ZMod 2} :
-- imply
  (∑ q : Fin 3 × (ZMod L × ZMod L), triangularFacePositiveCoeff lower upper q.1 q.2 * (triangularIntStep (triangularTorusPositiveDirection q.1)).1) = 0 := by
-- proof
  apply StatMech.FrontierA.triangularFacePositiveCoeff_full_fst_sum_eq_zero lower upper

/--
[triangularFacePositiveCoeff_full_snd_sum_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePrimitive.lean)
-/
@[path]
private lemma triangularFacePositiveCoeff_full_snd_sum_eq_zero_eq
  {L : Nat}
  [NeZero L]
  {lower upper : (ZMod L × ZMod L) → ZMod 2} :
-- imply
  (∑ q : Fin 3 × (ZMod L × ZMod L), triangularFacePositiveCoeff lower upper q.1 q.2 * (triangularIntStep (triangularTorusPositiveDirection q.1)).2) = 0 := by
-- proof
  apply StatMech.FrontierA.triangularFacePositiveCoeff_full_snd_sum_eq_zero lower upper

/--
[triangularZeroHomology_cycleBoundaryCoeff_mul_step_fst_sum_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePrimitive.lean)
-/
@[path]
private lemma triangularZeroHomology_cycleBoundaryCoeff_mul_step_fst_sum_eq_zero_eq
  {L : Nat}
  [Fact (2 < L)]
  {root : ZMod L × ZMod L}
  {p : (triangularTorusGraph L).Walk root root}
-- given
  (hp : p.IsCycle)
  (hhom : triangularTorusEvenHomology L p.edges.toFinset = 0) :
-- imply
  letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ (∑ k, triangularFaceBoundaryCoeff (triangularZeroHomologyLowerPotential L p.edges.toFinset) (triangularZeroHomologyUpperPotential L p.edges.toFinset) (triangularTorusCycleNativeDart L p k) * (triangularIntStep (triangularTorusCycleNativeDart L p k).2).1) = 0 := by
-- proof
  apply StatMech.FrontierA.triangularZeroHomology_cycleBoundaryCoeff_mul_step_fst_sum_eq_zero L p hp hhom

/--
[triangularZeroHomology_cycleBoundaryCoeff_mul_step_snd_sum_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePrimitive.lean)
-/
@[path]
private lemma triangularZeroHomology_cycleBoundaryCoeff_mul_step_snd_sum_eq_zero_eq
  {L : Nat}
  [Fact (2 < L)]
  {root : ZMod L × ZMod L}
  {p : (triangularTorusGraph L).Walk root root}
-- given
  (hp : p.IsCycle)
  (hhom : triangularTorusEvenHomology L p.edges.toFinset = 0) :
-- imply
  letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ (∑ k, triangularFaceBoundaryCoeff (triangularZeroHomologyLowerPotential L p.edges.toFinset) (triangularZeroHomologyUpperPotential L p.edges.toFinset) (triangularTorusCycleNativeDart L p k) * (triangularIntStep (triangularTorusCycleNativeDart L p k).2).2) = 0 := by
-- proof
  apply StatMech.FrontierA.triangularZeroHomology_cycleBoundaryCoeff_mul_step_snd_sum_eq_zero L p hp hhom

/--
[triangularTorus_simpleCycle_zeroEvenHomology_displacement_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePrimitive.lean)
-/
@[path]
private lemma triangularTorus_simpleCycle_zeroEvenHomology_displacement_eq_zero_eq
  {L : Nat}
  [Fact (2 < L)]
  {root : ZMod L × ZMod L}
  {p : (triangularTorusGraph L).Walk root root}
-- given
  (hp : p.IsCycle)
  (hhom : triangularTorusEvenHomology L p.edges.toFinset = 0) :
-- imply
  letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ (∑ k, triangularIntStep (triangularTorusCycleNativeDart L p k).2) = 0 := by
-- proof
  apply StatMech.FrontierA.triangularTorus_simpleCycle_zeroEvenHomology_displacement_eq_zero L p hp hhom

/--
[triangularTorus_zeroHomologyWinding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePrimitive.lean)
-/
@[path]
private lemma triangularTorus_zeroHomologyWinding_eq
  {L : Nat}
  [Fact (2 < L)] :
-- imply
  TriangularTorusZeroHomologyWinding L := by
-- proof
  apply StatMech.FrontierA.triangularTorus_zeroHomologyWinding L

/--
[triangularTorus_cyclePhaseProduct_eq_neg_baseSpinSign_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePrimitive.lean)
-/
@[path]
private lemma triangularTorus_cyclePhaseProduct_eq_neg_baseSpinSign_closed_eq
  {L : Nat}
  [Fact (2 < L)]
  {rho : Complex}
  {root : ZMod L × ZMod L}
  {p : (triangularTorusGraph L).Walk root root}
-- given
  (hrho : rho ^ 4 = Complex.I)
  (hp : p.IsCycle) :
-- imply
  letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ kwLoopPhaseProduct (triangularTorusGraphPhase L rho 1 1) (kwGraphCycleDartLoop p) = -(surfaceParitySign (surfaceQuadraticParity (triangularTorusSurfaceSpin 0 0) (surfaceSubgraphHomology (triangularTorusSurfaceEdgeClass L) p.edges.toFinset)) : Complex) := by
-- proof
  apply StatMech.FrontierA.triangularTorus_cyclePhaseProduct_eq_neg_baseSpinSign_closed L rho hrho p hp


-- created on 2026-10-23

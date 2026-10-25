import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.GeneralInteractionFreeParityLimit.Part6
open Filter MeasureTheory Set Topology StatMech StatMech.FrontierB


/--
[sym2_toFinset_map_embedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeParityLimit.lean)
-/
@[path]
private lemma sym2_toFinset_map_embedding_eq
  [DecidableEq V]
  [DecidableEq W]
  {f : V ↪ W}
  {e : Sym2 V} :
-- imply
  (Sym2.map f e).toFinset = e.toFinset.map f := by
-- proof
  apply StatMech.FrontierB.sym2_toFinset_map_embedding f e

/--
[finset_map_symmDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeParityLimit.lean)
-/
@[path]
private lemma finset_map_symmDiff_eq
  [DecidableEq V]
  [DecidableEq W]
  {f : V ↪ W}
  {A B : Finset V} :
-- imply
  (A ∆ B).map f = A.map f ∆ B.map f := by
-- proof
  apply StatMech.FrontierB.finset_map_symmDiff f A B

/--
[edgeBoundary_sym2FinsetMap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeParityLimit.lean)
-/
@[path]
private lemma edgeBoundary_sym2FinsetMap_eq
  [DecidableEq V]
  [DecidableEq W]
  {f : V ↪ W}
  {E : Finset (Sym2 V)} :
-- imply
  edgeBoundary (sym2FinsetMap f E) = (edgeBoundary E).map f := by
-- proof
  apply StatMech.FrontierB.edgeBoundary_sym2FinsetMap f E

/--
[interactionBoxLiftEdge_map_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeParityLimit.lean)
-/
@[path]
private lemma interactionBoxLiftEdge_map_val_eq
  {d n : Nat}
  {F : Finset (Sym2 (Site d))}
  {e : ↑F}
-- given
  (hFbox : ∀ e ∈ F, ∀ x ∈ e, x ∈ box d n) :
-- imply
  Sym2.map Subtype.val (interactionBoxLiftEdge F hFbox e) = e.1 := by
-- proof
  apply StatMech.FrontierB.interactionBoxLiftEdge_map_val F hFbox e

/--
[interactionBoxLiftedEdges_ambient_image](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeParityLimit.lean)
-/
@[path]
private lemma interactionBoxLiftedEdges_ambient_image_eq
  {d n : Nat}
  {F : Finset (Sym2 (Site d))}
-- given
  (hFbox : ∀ e ∈ F, ∀ x ∈ e, x ∈ box d n) :
-- imply
  sym2FinsetMap (Function.Embedding.subtype (fun x : Site d => x ∈ interactionBoxVertices d n)) (interactionBoxLiftedEdges F hFbox) = F := by
-- proof
  apply StatMech.FrontierB.interactionBoxLiftedEdges_ambient_image F hFbox

/--
[interactionBoxLiftedEdges_subset_edgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeParityLimit.lean)
-/
@[path]
private lemma interactionBoxLiftedEdges_subset_edgeFinset_eq
  {d n : Nat}
  {F : Finset (Sym2 (Site d))}
-- given
  (hFbox : ∀ e ∈ F, ∀ x ∈ e, x ∈ box d n)
  (hFdiag : ∀ e ∈ F, ¬e.IsDiag) :
-- imply
  interactionBoxLiftedEdges F hFbox ⊆ (interactionBoxGraph d n).edgeFinset := by
-- proof
  apply StatMech.FrontierB.interactionBoxLiftedEdges_subset_edgeFinset F hFbox hFdiag

/--
[preimage_currentParityAvoidCylinder_extendInteractionBoxCurrent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeParityLimit.lean)
-/
@[path]
private lemma preimage_currentParityAvoidCylinder_extendInteractionBoxCurrent_eq
  {d n : Nat}
  {E : Finset (Sym2 (interactionBoxVertices d n))}
-- given
  (hE : E ⊆ (interactionBoxGraph d n).edgeFinset) :
-- imply
  extendInteractionBoxCurrent d n ⁻¹' currentParityAvoidCylinder (sym2FinsetMap (Function.Embedding.subtype (fun x : Site d => x ∈ interactionBoxVertices d n)) E) = {m | Disjoint (currentParitySupport (interactionBoxGraph d n) m) E} := by
-- proof
  apply StatMech.FrontierB.preimage_currentParityAvoidCylinder_extendInteractionBoxCurrent d n E hE

/--
[measurableSet_currentParityAvoidCylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeParityLimit.lean)
-/
@[path]
private lemma measurableSet_currentParityAvoidCylinder_eq
  [Countable E]
  {F : Finset E} :
-- imply
  MeasurableSet (currentParityAvoidCylinder F) := by
-- proof
  apply StatMech.FrontierB.measurableSet_currentParityAvoidCylinder F

/--
[generalFreeBoxCurrentMeasure_parityAvoid_edgeImage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeParityLimit.lean)
-/
@[path]
private lemma generalFreeBoxCurrentMeasure_parityAvoid_edgeImage_eq
  {d n : Nat}
  {J : Sym2 (Site d) → ℝ}
  {beta : ℝ}
  {E : Finset (Sym2 (interactionBoxVertices d n))}
-- given
  (hJ : ∀ e, 0 ≤ J e)
  (hbeta : 0 < beta)
  (hE : E ⊆ (interactionBoxGraph d n).edgeFinset) :
-- imply
  (generalFreeBoxCurrentMeasure J hJ n beta hbeta.le : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) (currentParityAvoidCylinder (sym2FinsetMap (Function.Embedding.subtype (fun x : Site d => x ∈ interactionBoxVertices d n)) E)) = ENNReal.ofReal (expJ (interactionBoxGraph d n).edgeFinset (fun e => beta * interactionBoxCoupling J n e) (fun _ => 0) (fun s => Real.exp (-weightedEdgeSpinSum beta (interactionBoxCoupling J n) E s)) * ∏ e ∈ E, Real.cosh (beta * interactionBoxCoupling J n e)) := by
-- proof
  apply StatMech.FrontierB.generalFreeBoxCurrentMeasure_parityAvoid_edgeImage J hJ beta hbeta E hE

/--
[interactionBoxTransportedEdges_subset_edgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeParityLimit.lean)
-/
@[path]
private lemma interactionBoxTransportedEdges_subset_edgeFinset_eq
  {d : Nat}
  {n m : Nat}
  {E : Finset (Sym2 (interactionBoxVertices d n))}
-- given
  (hnm : n ≤ m)
  (hE : E ⊆ (interactionBoxGraph d n).edgeFinset) :
-- imply
  interactionBoxTransportedEdges d hnm E ⊆ (interactionBoxGraph d m).edgeFinset := by
-- proof
  apply StatMech.FrontierB.interactionBoxTransportedEdges_subset_edgeFinset d hnm E hE

/--
[interactionBoxTransportedEdges_ambient_image](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeParityLimit.lean)
-/
@[path]
private lemma interactionBoxTransportedEdges_ambient_image_eq
  {d : Nat}
  {n m : Nat}
  {E : Finset (Sym2 (interactionBoxVertices d n))}
-- given
  (hnm : n ≤ m) :
-- imply
  sym2FinsetMap (Function.Embedding.subtype (fun x : Site d => x ∈ interactionBoxVertices d m)) (interactionBoxTransportedEdges d hnm E) = sym2FinsetMap (Function.Embedding.subtype (fun x : Site d => x ∈ interactionBoxVertices d n)) E := by
-- proof
  apply StatMech.FrontierB.interactionBoxTransportedEdges_ambient_image d hnm E

/--
[interactionBoxSpinSupport_map_base](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeParityLimit.lean)
-/
@[path]
private lemma interactionBoxSpinSupport_map_base_eq
  {d : Nat}
  {n m : Nat}
  {A : Finset (interactionBoxVertices d n)}
-- given
  (hnm : n ≤ m) :
-- imply
  interactionBoxSpinSupport d m (A.map (Function.Embedding.subtype (fun x : Site d => x ∈ interactionBoxVertices d n))) = A.map (interactionBoxVertexIncl d hnm) := by
-- proof
  apply StatMech.FrontierB.interactionBoxSpinSupport_map_base d hnm A

/--
[interactionBoxCoupling_transport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeParityLimit.lean)
-/
@[path]
private lemma interactionBoxCoupling_transport_eq
  {d : Nat}
  {J : Sym2 (Site d) → ℝ}
  {n m : Nat}
  {e : Sym2 (interactionBoxVertices d n)}
-- given
  (hnm : n ≤ m) :
-- imply
  interactionBoxCoupling J m (Sym2.map (interactionBoxVertexIncl d hnm) e) = interactionBoxCoupling J n e := by
-- proof
  apply StatMech.FrontierB.interactionBoxCoupling_transport J hnm e

/--
[bond_transport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeParityLimit.lean)
-/
@[path]
private lemma bond_transport_eq
  {d : Nat}
  {n m : Nat}
  {s : ConfigSpace (interactionBoxVertices d m)}
  {e : Sym2 (interactionBoxVertices d n)}
-- given
  (hnm : n ≤ m) :
-- imply
  bond s (Sym2.map (interactionBoxVertexIncl d hnm) e) = bond (fun x => s (interactionBoxVertexIncl d hnm x)) e := by
-- proof
  apply StatMech.FrontierB.bond_transport hnm s e

/--
[spinProd_transport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeParityLimit.lean)
-/
@[path]
private lemma spinProd_transport_eq
  {d : Nat}
  {n m : Nat}
  {s : ConfigSpace (interactionBoxVertices d m)}
  {A : Finset (interactionBoxVertices d n)}
-- given
  (hnm : n ≤ m) :
-- imply
  spinProd A (fun x => s (interactionBoxVertexIncl d hnm x)) = spinProd (A.map (interactionBoxVertexIncl d hnm)) s := by
-- proof
  apply StatMech.FrontierB.spinProd_transport hnm s A

/--
[weightedEdgeSpinSum_transport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeParityLimit.lean)
-/
@[path]
private lemma weightedEdgeSpinSum_transport_eq
  {d : Nat}
  {J : Sym2 (Site d) → ℝ}
  {beta : ℝ}
  {n m : Nat}
  {E : Finset (Sym2 (interactionBoxVertices d n))}
  {s : ConfigSpace (interactionBoxVertices d m)}
-- given
  (hnm : n ≤ m) :
-- imply
  weightedEdgeSpinSum beta (interactionBoxCoupling J m) (interactionBoxTransportedEdges d hnm E) s = weightedEdgeSpinSum beta (interactionBoxCoupling J n) E (fun x => s (interactionBoxVertexIncl d hnm x)) := by
-- proof
  apply StatMech.FrontierB.weightedEdgeSpinSum_transport J beta hnm E s

/--
[exp_neg_weightedEdgeSpinSum_transport_expansion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeParityLimit.lean)
-/
@[path]
private lemma exp_neg_weightedEdgeSpinSum_transport_expansion_eq
  {d : Nat}
  {J : Sym2 (Site d) → ℝ}
  {beta : ℝ}
  {n m : Nat}
  {E : Finset (Sym2 (interactionBoxVertices d n))}
  {s : ConfigSpace (interactionBoxVertices d m)}
-- given
  (hnm : n ≤ m)
  (hEdiag : ∀ e ∈ E, ¬e.IsDiag) :
-- imply
  Real.exp (-weightedEdgeSpinSum beta (interactionBoxCoupling J m) (interactionBoxTransportedEdges d hnm E) s) = ∑ T ∈ E.powerset, weightedEdgeExpansionCoeff beta (interactionBoxCoupling J n) E T * spinProd ((edgeBoundary (E \ T)).map (interactionBoxVertexIncl d hnm)) s := by
-- proof
  apply StatMech.FrontierB.exp_neg_weightedEdgeSpinSum_transport_expansion J beta hnm E hEdiag s

/--
[expJ_transport_expansion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeParityLimit.lean)
-/
@[path]
private lemma expJ_transport_expansion_eq
  {d : Nat}
  {J : Sym2 (Site d) → ℝ}
  {beta : ℝ}
  {n m : Nat}
  {E : Finset (Sym2 (interactionBoxVertices d n))}
-- given
  (hnm : n ≤ m)
  (hEdiag : ∀ e ∈ E, ¬e.IsDiag) :
-- imply
  expJ (interactionBoxGraph d m).edgeFinset (fun e => beta * interactionBoxCoupling J m e) (fun _ => 0) (fun s => Real.exp (-weightedEdgeSpinSum beta (interactionBoxCoupling J m) (interactionBoxTransportedEdges d hnm E) s)) = ∑ T ∈ E.powerset, weightedEdgeExpansionCoeff beta (interactionBoxCoupling J n) E T * expJ (interactionBoxGraph d m).edgeFinset (fun e => beta * interactionBoxCoupling J m e) (fun _ => 0) (spinProd ((edgeBoundary (E \ T)).map (interactionBoxVertexIncl d hnm))) := by
-- proof
  apply StatMech.FrontierB.expJ_transport_expansion J beta hnm E hEdiag

/--
[cosh_product_transport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeParityLimit.lean)
-/
@[path]
private lemma cosh_product_transport_eq
  {d : Nat}
  {J : Sym2 (Site d) → ℝ}
  {beta : ℝ}
  {n m : Nat}
  {E : Finset (Sym2 (interactionBoxVertices d n))}
-- given
  (hnm : n ≤ m) :
-- imply
  (∏ e ∈ interactionBoxTransportedEdges d hnm E, Real.cosh (beta * interactionBoxCoupling J m e)) = ∏ e ∈ E, Real.cosh (beta * interactionBoxCoupling J n e) := by
-- proof
  apply StatMech.FrontierB.cosh_product_transport J beta hnm E

/--
[finiteInteractionEdges_subset_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeParityLimit.lean)
-/
@[path]
private lemma finiteInteractionEdges_subset_box_eq
  {d : Nat}
  {F : Finset (Sym2 (Site d))} :
-- imply
  ∃ N, ∀ e ∈ F, ∀ x ∈ e, x ∈ box d N := by
-- proof
  apply StatMech.FrontierB.finiteInteractionEdges_subset_box F

/--
[generalFreeBoxCurrentMeasure_parityAvoid_full_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeParityLimit.lean)
-/
@[path]
private lemma generalFreeBoxCurrentMeasure_parityAvoid_full_tendsto_eq
  {d : Nat}
  {J : Sym2 (Site d) → ℝ}
  {beta : ℝ}
  {F : Finset (Sym2 (Site d))}
-- given
  (hJ : ∀ e, 0 ≤ J e)
  (hbeta : 0 < beta)
  (hFdiag : ∀ e ∈ F, ¬e.IsDiag) :
-- imply
  ∃ L : ℝ≥0∞, Tendsto (fun n => (generalFreeBoxCurrentMeasure J hJ n beta hbeta.le : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) (currentParityAvoidCylinder F)) atTop (nhds L) := by
-- proof
  apply StatMech.FrontierB.generalFreeBoxCurrentMeasure_parityAvoid_full_tendsto J hJ beta hbeta F hFdiag

/--
[diagonal_not_mem_range_interactionBoxEdgeIncl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeParityLimit.lean)
-/
@[path]
private lemma diagonal_not_mem_range_interactionBoxEdgeIncl_eq
  {d n : Nat}
  {e : Sym2 (Site d)}
-- given
  (he : e.IsDiag) :
-- imply
  e ∉ Set.range (interactionBoxEdgeIncl d n) := by
-- proof
  apply StatMech.FrontierB.diagonal_not_mem_range_interactionBoxEdgeIncl d n e he

/--
[extendInteractionBoxCurrent_diag_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeParityLimit.lean)
-/
@[path]
private lemma extendInteractionBoxCurrent_diag_zero_eq
  {d n : Nat}
  {m : EdgeCurrent (interactionBoxGraph d n)}
  {e : Sym2 (Site d)}
-- given
  (he : e.IsDiag) :
-- imply
  extendInteractionBoxCurrent d n m e = 0 := by
-- proof
  apply StatMech.FrontierB.extendInteractionBoxCurrent_diag_zero d n m e he

/--
[preimage_currentParityAvoidCylinder_nonDiagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeParityLimit.lean)
-/
@[path]
private lemma preimage_currentParityAvoidCylinder_nonDiagonal_eq
  {d n : Nat}
  {F : Finset (Sym2 (Site d))} :
-- imply
  extendInteractionBoxCurrent d n ⁻¹' currentParityAvoidCylinder F = extendInteractionBoxCurrent d n ⁻¹' currentParityAvoidCylinder (nonDiagonalEdgeFinset F) := by
-- proof
  apply StatMech.FrontierB.preimage_currentParityAvoidCylinder_nonDiagonal d n F

/--
[generalFreeBoxCurrentMeasure_parityAvoid_nonDiagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeParityLimit.lean)
-/
@[path]
private lemma generalFreeBoxCurrentMeasure_parityAvoid_nonDiagonal_eq
  {d : Nat}
  {J : Sym2 (Site d) → ℝ}
  {beta : ℝ}
  {n : Nat}
  {F : Finset (Sym2 (Site d))}
-- given
  (hJ : ∀ e, 0 ≤ J e)
  (hbeta : 0 ≤ beta) :
-- imply
  (generalFreeBoxCurrentMeasure J hJ n beta hbeta : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) (currentParityAvoidCylinder F) = (generalFreeBoxCurrentMeasure J hJ n beta hbeta : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) (currentParityAvoidCylinder (nonDiagonalEdgeFinset F)) := by
-- proof
  apply StatMech.FrontierB.generalFreeBoxCurrentMeasure_parityAvoid_nonDiagonal J hJ beta hbeta n F

/--
[generalFreeBoxCurrentMeasure_parityAvoid_full_tendsto_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeParityLimit.lean)
-/
@[path]
private lemma generalFreeBoxCurrentMeasure_parityAvoid_full_tendsto_all_eq
  {d : Nat}
  {J : Sym2 (Site d) → ℝ}
  {beta : ℝ}
  {F : Finset (Sym2 (Site d))}
-- given
  (hJ : ∀ e, 0 ≤ J e)
  (hbeta : 0 < beta) :
-- imply
  ∃ L : ℝ≥0∞, Tendsto (fun n => (generalFreeBoxCurrentMeasure J hJ n beta hbeta.le : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) (currentParityAvoidCylinder F)) atTop (nhds L) := by
-- proof
  apply StatMech.FrontierB.generalFreeBoxCurrentMeasure_parityAvoid_full_tendsto_all J hJ beta hbeta F


-- created on 2026-10-23

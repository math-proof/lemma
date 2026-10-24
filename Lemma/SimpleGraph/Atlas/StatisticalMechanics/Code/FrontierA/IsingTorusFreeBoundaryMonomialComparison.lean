import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingTorusFreeBoundaryMonomialComparison
open Finset StatMech StatMech.FrontierA


/--
[finiteCutConditionalSpinProd_le_plus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusFreeBoundaryMonomialComparison.lean)
-/
@[path]
private lemma finiteCutConditionalSpinProd_le_plus_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {S : Finset V}
-- given
  (hbeta : 0 ≤ beta)
  (outside : {v : V // v ∉ S} → Bool)
  (A : Finset {v : V // v ∈ S}) :
-- imply
  finiteCutConditionalSpinProd G beta S outside A ≤ finiteCutPlusSpinProd G beta S A := by
-- proof
  apply StatMech.FrontierA.finiteCutConditionalSpinProd_le_plus G beta hbeta S outside A

/--
[finiteCutConditionalSpinProd_eq_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusFreeBoundaryMonomialComparison.lean)
-/
@[path]
private lemma finiteCutConditionalSpinProd_eq_div_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {S : Finset V}
-- given
  (outside : {v : V // v ∉ S} → Bool)
  (A : Finset {v : V // v ∈ S}) :
-- imply
  finiteCutConditionalSpinProd G beta S outside A = finiteCutConditionalSpinProdNumerator G beta S outside A / finiteCutConditionalZ G beta S outside := by
-- proof
  apply StatMech.FrontierA.finiteCutConditionalSpinProd_eq_div G beta S outside A

/--
[spinProd_map_subtype_finiteCutMerge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusFreeBoundaryMonomialComparison.lean)
-/
@[path]
private lemma spinProd_map_subtype_finiteCutMerge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
-- given
  (inside : {v : V // v ∈ S} → Bool)
  (outside : {v : V // v ∉ S} → Bool)
  (A : Finset {v : V // v ∈ S}) :
-- imply
  spinProd (A.map (Function.Embedding.subtype fun v ↦ v ∈ S)) (finiteCutMerge S inside outside) = spinProd A inside := by
-- proof
  apply StatMech.FrontierA.spinProd_map_subtype_finiteCutMerge G S inside outside A

/--
[sum_spinProd_wJ_eq_sum_finiteCutExteriorFactor_mul_conditionalNumerator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusFreeBoundaryMonomialComparison.lean)
-/
@[path]
private lemma sum_spinProd_wJ_eq_sum_finiteCutExteriorFactor_mul_conditionalNumerator_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {S : Finset V}
-- given
  (A : Finset {v : V // v ∈ S}) :
-- imply
  (∑ sigma : ConfigSpace V, spinProd (A.map (Function.Embedding.subtype fun v ↦ v ∈ S)) sigma * wJ G.edgeFinset (fun _ ↦ beta) (fun _ ↦ 0) sigma) = ∑ outside : {v : V // v ∉ S} → Bool, finiteCutExteriorFactor G beta S outside * finiteCutConditionalSpinProdNumerator G beta S outside A := by
-- proof
  apply StatMech.FrontierA.sum_spinProd_wJ_eq_sum_finiteCutExteriorFactor_mul_conditionalNumerator G beta S A

/--
[expJ_spinProd_le_finiteCutPlusSpinProd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusFreeBoundaryMonomialComparison.lean)
-/
@[path]
private lemma expJ_spinProd_le_finiteCutPlusSpinProd_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {S : Finset V}
-- given
  (hbeta : 0 ≤ beta)
  (A : Finset {v : V // v ∈ S}) :
-- imply
  expJ G.edgeFinset (fun _ ↦ beta) (fun _ ↦ 0) (spinProd (A.map (Function.Embedding.subtype fun v ↦ v ∈ S))) ≤ finiteCutPlusSpinProd G beta S A := by
-- proof
  apply StatMech.FrontierA.expJ_spinProd_le_finiteCutPlusSpinProd G beta hbeta S A

/--
[expJ_spinProd_const_relabel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusFreeBoundaryMonomialComparison.lean)
-/
@[path]
private lemma expJ_spinProd_const_relabel_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype W]
  [DecidableEq W]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {e : V ≃ W}
  {beta : Real}
  {fieldV : V → Real}
  {fieldW : W → Real}
  {A : Finset V}
-- given
  (hadj : ∀ x y, G.Adj x y ↔ H.Adj (e x) (e y))
  (hfield : ∀ x, fieldV x = fieldW (e x)) :
-- imply
  expJ G.edgeFinset (fun _ ↦ beta) fieldV (spinProd A) = expJ H.edgeFinset (fun _ ↦ beta) fieldW (spinProd (A.map e.toEmbedding)) := by
-- proof
  apply StatMech.FrontierA.expJ_spinProd_const_relabel G H e hadj beta fieldV fieldW hfield A

/--
[finiteCutPlusSpinProd_relabel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusFreeBoundaryMonomialComparison.lean)
-/
@[path]
private lemma finiteCutPlusSpinProd_relabel_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype W]
  [DecidableEq W]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {S : Finset V}
  {T : Finset W}
  {beta : Real}
-- given
  (e : {v : V // v ∈ S} ≃ {w : W // w ∈ T})
  (hadj : ∀ x y, (finiteCutGraph G S).Adj x y ↔ (finiteCutGraph H T).Adj (e x) (e y))
  (hfield : ∀ x, finiteCutPlusBoundaryField G S x = finiteCutPlusBoundaryField H T (e x))
  (A : Finset {v : V // v ∈ S}) :
-- imply
  finiteCutPlusSpinProd G beta S A = finiteCutPlusSpinProd H beta T (A.map e.toEmbedding) := by
-- proof
  apply StatMech.FrontierA.finiteCutPlusSpinProd_relabel G H S T e hadj hfield beta A

/--
[expJ_spinProd_beta_field_eq_vertexFieldExpectation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusFreeBoundaryMonomialComparison.lean)
-/
@[path]
private lemma expJ_spinProd_beta_field_eq_vertexFieldExpectation_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {field : V → Real}
  {A : Finset V} :
-- imply
  expJ G.edgeFinset (fun _ ↦ beta) (fun z ↦ beta * field z) (spinProd A) = vertexFieldExpectation G beta (unitEdgeCoupling G) field (spinProd A) := by
-- proof
  apply StatMech.FrontierA.expJ_spinProd_beta_field_eq_vertexFieldExpectation G beta field A

/--
[integral_gvPlus_spinProd_eq_vertexFieldExpectation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusFreeBoundaryMonomialComparison.lean)
-/
@[path]
private lemma integral_gvPlus_spinProd_eq_vertexFieldExpectation_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : Nat}
  {S : Finset (Site d)}
  {beta : Real}
-- given
  (A : Finset {v : Site d // v ∈ S}) :
-- imply
  (∫ omega, spinProd (A.map (Function.Embedding.subtype fun v ↦ v ∈ S)) omega ∂(gvPlusMeasure S beta 0)) = vertexFieldExpectation (graphS d S) beta (unitEdgeCoupling (graphS d S)) (plusBoundaryField S) (spinProd A) := by
-- proof
  apply StatMech.FrontierA.integral_gvPlus_spinProd_eq_vertexFieldExpectation G S beta A

/--
[finiteCutPlusSpinProd_torusImage_eq_gvPlus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusFreeBoundaryMonomialComparison.lean)
-/
@[path]
private lemma finiteCutPlusSpinProd_torusImage_eq_gvPlus_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d k R : Nat}
  {S : Finset (Site d)}
  {beta : Real}
-- given
  (hS : (↑S : Set (Site d)) ⊆ box d R)
  (hside : 2 * (R + 1) < isingDyadicSide k)
  (hinj : Set.InjOn (isingSiteToDyadicTorus k) (↑S : Set (Site d)))
  (A : Finset {x // x ∈ S}) :
-- imply
  finiteCutPlusSpinProd (isingTorusGraph d k) beta (isingTorusImageFinset k S) (A.map (isingTorusImageEquiv S hinj).toEmbedding) = ∫ omega, spinProd (A.map (Function.Embedding.subtype fun v ↦ v ∈ S)) omega ∂(gvPlusMeasure S beta 0) := by
-- proof
  apply StatMech.FrontierA.finiteCutPlusSpinProd_torusImage_eq_gvPlus G S hS hside hinj beta A

/--
[freeSpinProd_le_isingTorusSpinProd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusFreeBoundaryMonomialComparison.lean)
-/
@[path]
private lemma freeSpinProd_le_isingTorusSpinProd_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d k R : Nat}
  {S : Finset (Site d)}
  {beta : Real}
-- given
  (hS : (↑S : Set (Site d)) ⊆ box d R)
  (hside : 2 * (R + 1) < isingDyadicSide k)
  (hbeta : 0 ≤ beta)
  (A : Finset {x // x ∈ S}) :
-- imply
  isingExpectation (graphS d S) beta 0 (spinProd A) ≤ expJ (isingTorusGraph d k).edgeFinset (fun _ ↦ beta) (fun _ ↦ 0) (spinProd ((A.map (isingTorusImageEquiv S (isingSiteToDyadicTorus_injectiveOn_finset S hS (lt_of_lt_of_le (by omega : 2 * R < 2 * (R + 1)) hside.le))).toEmbedding).map (Function.Embedding.subtype fun z ↦ z ∈ isingTorusImageFinset k S))) := by
-- proof
  apply StatMech.FrontierA.freeSpinProd_le_isingTorusSpinProd G S hS hside beta hbeta A

/--
[freeSpinProd_le_isingTorusSpinProd_le_gvPlus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusFreeBoundaryMonomialComparison.lean)
-/
@[path]
private lemma freeSpinProd_le_isingTorusSpinProd_le_gvPlus_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d k R : Nat}
  {S : Finset (Site d)}
  {beta : Real}
-- given
  (hS : (↑S : Set (Site d)) ⊆ box d R)
  (hside : 2 * (R + 1) < isingDyadicSide k)
  (hinj : Set.InjOn (isingSiteToDyadicTorus k) (↑S : Set (Site d)))
  (hbeta : 0 ≤ beta)
  (A : Finset {x // x ∈ S}) :
-- imply
  isingExpectation (graphS d S) beta 0 (spinProd A) ≤ expJ (isingTorusGraph d k).edgeFinset (fun _ ↦ beta) (fun _ ↦ 0) (spinProd ((A.map (isingTorusImageEquiv S hinj).toEmbedding).map (Function.Embedding.subtype fun z ↦ z ∈ isingTorusImageFinset k S))) ∧ expJ (isingTorusGraph d k).edgeFinset (fun _ ↦ beta) (fun _ ↦ 0) (spinProd ((A.map (isingTorusImageEquiv S hinj).toEmbedding).map (Function.Embedding.subtype fun z ↦ z ∈ isingTorusImageFinset k S))) ≤ ∫ omega, spinProd (A.map (Function.Embedding.subtype fun v ↦ v ∈ S)) omega ∂(gvPlusMeasure S beta 0) := by
-- proof
  apply StatMech.FrontierA.freeSpinProd_le_isingTorusSpinProd_le_gvPlus G S hS hside hinj beta hbeta A


-- created on 2026-10-23

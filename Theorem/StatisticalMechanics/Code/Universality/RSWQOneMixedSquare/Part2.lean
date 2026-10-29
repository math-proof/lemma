/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWQOneMixedSquare.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWStripSymmetry.Part5
import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part101
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.IvProperties
import Theorem.StatisticalMechanics.Code.Percolation.PcUpperViaFK.Part4
import Theorem.StatisticalMechanics.Code.Percolation.OffClusterIndep.Part4
import Theorem.StatisticalMechanics.Code.Probability.InhomogeneousProduct.Part2
import Def.StatisticalMechanics.Code.Universality.RSWQOneMixedSquare
open Set SimpleGraph MeasureTheory
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Lattice

open StatMech.FK

open StatMech.RSW.Box

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem rq1_centeredRect_subset_box (n : ℕ) :
    rect (-(n : ℤ)) (n : ℤ) (-(n : ℤ)) (n : ℤ) ⊆ box 2 n := by
  intro z hz
  rw [mem_rect] at hz
  rw [mem_box]
  intro i
  fin_cases i
  · change (z 0).natAbs ≤ n
    by_cases h0 : 0 ≤ z 0
    · have hcast : (((z 0).natAbs : ℕ) : ℤ) = z 0 :=
        Int.natAbs_of_nonneg h0
      omega
    · have hcast : (((z 0).natAbs : ℕ) : ℤ) = -z 0 := by
        rw [← Int.natAbs_neg]
        exact Int.natAbs_of_nonneg (by omega)
      omega
  · change (z 1).natAbs ≤ n
    by_cases h1 : 0 ≤ z 1
    · have hcast : (((z 1).natAbs : ℕ) : ℤ) = z 1 :=
        Int.natAbs_of_nonneg h1
      omega
    · have hcast : (((z 1).natAbs : ℕ) : ℤ) = -z 1 := by
        rw [← Int.natAbs_neg]
        exact Int.natAbs_of_nonneg (by omega)
      omega

theorem rq1_extendEdge_centered_pair (n : ℕ)
    (eta : ConfigSpace (Sym2 (boxVerts 2 n))) {x y : Site 2}
    (hx : x ∈ rect (-(n : ℤ)) (n : ℤ) (-(n : ℤ)) (n : ℤ))
    (hy : y ∈ rect (-(n : ℤ)) (n : ℤ) (-(n : ℤ)) (n : ℤ)) :
    extendEdge 2 n eta s(x, y) =
      eta s((⟨x, rq1_centeredRect_subset_box n hx⟩ : boxVerts 2 n),
        (⟨y, rq1_centeredRect_subset_box n hy⟩ : boxVerts 2 n)) := by
  let xb : boxVerts 2 n := ⟨x, rq1_centeredRect_subset_box n hx⟩
  let yb : boxVerts 2 n := ⟨y, rq1_centeredRect_subset_box n hy⟩
  have heq : edgeIncl 2 n s(xb, yb) = s(x, y) := by
    simp [edgeIncl, Sym2.map_mk, xb, yb]
  rw [← heq, extendEdge_eq_of_range]


theorem rq1_finiteMixedSquareEvent_dependsOn (n : ℕ) :
    _root_.DependsOn
      ((rq1_finiteMixedSquareEvent n).indicator (fun _ => (1 : ℝ)))
      ((boxGraph 2 n).edgeFinset : Set (Sym2 (boxVerts 2 n))) := by
  intro eta eta' hagree
  have hgraph : openSubgraphInduce 2 (extendEdge 2 n eta)
        (rect (-(n : ℤ)) (n : ℤ) (-(n : ℤ)) (n : ℤ)) =
      openSubgraphInduce 2 (extendEdge 2 n eta')
        (rect (-(n : ℤ)) (n : ℤ) (-(n : ℤ)) (n : ℤ)) := by
    apply SimpleGraph.ext
    ext x y
    simp only [openSubgraphInduce_adj, openSubgraph_adj]
    constructor
    · rintro ⟨hadj, hopen⟩
      refine ⟨hadj, ?_⟩
      let xb : boxVerts 2 n := ⟨x, rq1_centeredRect_subset_box n x.2⟩
      let yb : boxVerts 2 n := ⟨y, rq1_centeredRect_subset_box n y.2⟩
      have hbe : s(xb, yb) ∈ (boxGraph 2 n).edgeFinset := by
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, boxGraph,
          SimpleGraph.comap_adj]
        exact hadj
      have heq := hagree s(xb, yb) hbe
      rw [rq1_extendEdge_centered_pair n eta x.2 y.2] at hopen
      rw [rq1_extendEdge_centered_pair n eta' x.2 y.2]
      exact heq ▸ hopen
    · rintro ⟨hadj, hopen⟩
      refine ⟨hadj, ?_⟩
      let xb : boxVerts 2 n := ⟨x, rq1_centeredRect_subset_box n x.2⟩
      let yb : boxVerts 2 n := ⟨y, rq1_centeredRect_subset_box n y.2⟩
      have hbe : s(xb, yb) ∈ (boxGraph 2 n).edgeFinset := by
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, boxGraph,
          SimpleGraph.comap_adj]
        exact hadj
      have heq := hagree s(xb, yb) hbe
      rw [rq1_extendEdge_centered_pair n eta' x.2 y.2] at hopen
      rw [rq1_extendEdge_centered_pair n eta x.2 y.2]
      exact heq.symm ▸ hopen
  have hevent : eta ∈ rq1_finiteMixedSquareEvent n ↔
      eta' ∈ rq1_finiteMixedSquareEvent n := by
    change HorizontalCrossing (extendEdge 2 n eta) _ _ _ _ ↔
      HorizontalCrossing (extendEdge 2 n eta') _ _ _ _
    unfold HorizontalCrossing ConnectedWithin
    rw [hgraph]
  by_cases heta : eta ∈ rq1_finiteMixedSquareEvent n
  · rw [Set.indicator_of_mem heta, Set.indicator_of_mem (hevent.mp heta)]
  · rw [Set.indicator_of_notMem heta,
      Set.indicator_of_notMem (fun h => heta (hevent.mpr h))]

theorem rq1_extend_restrict_centered_pair (n : ℕ)
    (omega : ConfigSpace (Sym2 (Site 2))) {x y : Site 2}
    (hx : x ∈ rect (-(n : ℤ)) (n : ℤ) (-(n : ℤ)) (n : ℤ))
    (hy : y ∈ rect (-(n : ℤ)) (n : ℤ) (-(n : ℤ)) (n : ℤ)) :
    extendEdge 2 n (boxRestrict 2 n omega) s(x, y) = omega s(x, y) := by
  rw [rq1_extendEdge_centered_pair n (boxRestrict 2 n omega) hx hy]
  simp [boxRestrict, edgeIncl, Sym2.map_mk]


theorem rq1_finiteMixedSquareEvent_preimage (n : ℕ) :
    boxRestrict 2 n ⁻¹' rq1_finiteMixedSquareEvent n =
      horizontalCrossingEvent (-(n : ℤ)) (n : ℤ) (-(n : ℤ)) (n : ℤ) := by
  ext omega
  change HorizontalCrossing (extendEdge 2 n (boxRestrict 2 n omega)) _ _ _ _ ↔
    HorizontalCrossing omega _ _ _ _
  constructor
  · rintro ⟨x, y, hxy⟩
    refine ⟨x, y, ?_⟩
    exact (StatMech.Percolation.connWithinR_congr
      (rect (-(n : ℤ)) (n : ℤ) (-(n : ℤ)) (n : ℤ))
      (leftSide_subset x.2) (rightSide_subset y.2)
      (fun u hu v hv => rq1_extend_restrict_centered_pair n omega hu hv)).mp hxy
  · rintro ⟨x, y, hxy⟩
    refine ⟨x, y, ?_⟩
    exact (StatMech.Percolation.connWithinR_congr
      (rect (-(n : ℤ)) (n : ℤ) (-(n : ℤ)) (n : ℤ))
      (leftSide_subset x.2) (rightSide_subset y.2)
      (fun u hu v hv => rq1_extend_restrict_centered_pair n omega hu hv)).mpr hxy


theorem rq1_centeredSquare_crossing_half (n : ℕ) (hn : 0 < n) :
    (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real
      (horizontalCrossingEvent (-(n : ℤ)) (n : ℤ) (-(n : ℤ)) (n : ℤ)) := by
  have hbase := rlc_square_half (2 * (n : ℤ)) (by omega)
  have htrans := cti_horizontalCrossing_translation_invariant
    0 (2 * (n : ℤ)) 0 (2 * (n : ℤ))
    (![-(n : ℤ), -(n : ℤ)] : Site 2)
    (rlc_horizontalCrossing_measurableSet 0 (2 * (n : ℤ)) 0 (2 * (n : ℤ)))
  have heq : rba_selfDualMeasure.real
      (horizontalCrossingEvent (-(n : ℤ)) (n : ℤ) (-(n : ℤ)) (n : ℤ)) =
      rba_selfDualMeasure.real
        (horizontalCrossingEvent 0 (2 * (n : ℤ)) 0 (2 * (n : ℤ))) := by
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      zero_add, show 2 * (n : ℤ) + -(n : ℤ) = n by ring] using htrans
  rwa [heq]


theorem rq1_finiteBernoulli_mixedSquare_eq (n : ℕ) :
    (bernoulliProductMeasure (E := Sym2 (boxVerts 2 n))
      (2⁻¹ : NNReal) half_le_one).real (rq1_finiteMixedSquareEvent n) =
      rba_selfDualMeasure.real
        (horizontalCrossingEvent (-(n : ℤ)) (n : ℤ) (-(n : ℤ)) (n : ℤ)) := by
  have hrestrict := bernoulliProduct_boxRestrict_preimage
    (d := 2) (2⁻¹ : NNReal) half_le_one n (rq1_finiteMixedSquareEvent n)
  rw [rq1_finiteMixedSquareEvent_preimage] at hrestrict
  simpa [rba_selfDualMeasure] using hrestrict.symm


theorem rq1_bcMixedSquare_crossing_half (n : ℕ) (hn : 0 < n)
    (C : SimpleGraph (boxVerts 2 n)) [DecidableRel C.Adj] :
    (1 : ℝ) / 2 ≤
      ∑ eta : ConfigSpace (Sym2 (boxVerts 2 n)),
        (rq1_finiteMixedSquareEvent n).indicator (fun _ => (1 : ℝ)) eta *
          bcProb (boxGraph 2 n) C ((1 : ℝ) / 2) 1 eta := by
  simp_rw [rq1_bcProb_one_eq_fkProb (boxGraph 2 n) C ((1 : ℝ) / 2)]
  calc
    (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real
        (horizontalCrossingEvent (-(n : ℤ)) (n : ℤ) (-(n : ℤ)) (n : ℤ)) :=
      rq1_centeredSquare_crossing_half n hn
    _ = (bernoulliProductMeasure (E := Sym2 (boxVerts 2 n))
          (2⁻¹ : NNReal) half_le_one).real (rq1_finiteMixedSquareEvent n) :=
      (rq1_finiteBernoulli_mixedSquare_eq n).symm
    _ = ∑ eta : ConfigSpace (Sym2 (boxVerts 2 n)),
        (rq1_finiteMixedSquareEvent n).indicator (fun _ => (1 : ℝ)) eta *
          fkProb (boxGraph 2 n) ((1 : ℝ) / 2) 1 eta := by
      symm
      rw [← rq1_halfBernoulliMeasure_eq]
      exact fkProbOne_event_eq_bernoulli (boxGraph 2 n)
        (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 : ℝ) / 2 < 1)
        (rq1_finiteMixedSquareEvent n) (rq1_finiteMixedSquareEvent_dependsOn n)


end Universality
end StatMech

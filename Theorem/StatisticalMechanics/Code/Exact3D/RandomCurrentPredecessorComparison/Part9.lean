/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part8
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

theorem doubledBoxOriginToInnerEndpointSource_eq_of_boxVertHasCoords3
    {n : ℕ} {v w : FK.boxVerts 3 n} {x y z : ℤ}
    (hv : boxVertHasCoords3 v x y z)
    (hw : boxVertHasCoords3 w x y z) :
    doubledBoxOriginToInnerEndpointSource n v =
      doubledBoxOriginToInnerEndpointSource n w := by
  rw [boxVert_eq_of_hasCoords3 hv hw]


theorem doubledBoxOriginToInnerEndpointSource_map_eq_of_maps_origin_endpoint
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (φ : FK.boxVerts 3 (2 * n) ≃ FK.boxVerts 3 (2 * n))
    (horigin :
      φ (IsingFK.boxOrigin 3 (2 * n)) =
        IsingFK.boxOrigin 3 (2 * n))
    (hend :
      φ (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v) =
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    (doubledBoxOriginToInnerEndpointSource n v).map φ.toEmbedding =
      doubledBoxOriginToInnerEndpointSource n w := by
  have horigin_symm : φ.symm (IsingFK.boxOrigin 3 (2 * n)) =
      IsingFK.boxOrigin 3 (2 * n) := by
    have h := congrArg φ.symm horigin
    simpa using h.symm
  have hend_symm :
      φ.symm (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) =
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v := by
    have h := congrArg φ.symm hend
    simpa using h.symm
  ext x
  have h0x : φ.symm x = IsingFK.boxOrigin 3 (2 * n) ↔
      x = IsingFK.boxOrigin 3 (2 * n) := by
    constructor
    · intro hx
      have h := congrArg φ hx
      simpa [horigin] using h
    · intro hx
      simp [hx, horigin_symm]
  have h1x :
      φ.symm x = FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ↔
        x = FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w := by
    constructor
    · intro hx
      have h := congrArg φ hx
      simpa [hend] using h
    · intro hx
      simp [hx, hend_symm]
  simp [doubledBoxOriginToInnerEndpointSource, Finset.mem_symmDiff, h0x, h1x]

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpointSource_map_eq_strictSectorPredecessor_of_maps_origin_endpoint
    {n : ℕ}
    (p :
      {v : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n v ∧
          ((v : Lattice.Site 3) (1 : Fin 3)) <
            ((v : Lattice.Site 3) (2 : Fin 3))})
    (φ : FK.boxVerts 3 (2 * n) ≃ FK.boxVerts 3 (2 * n))
    (horigin :
      φ (IsingFK.boxOrigin 3 (2 * n)) =
        IsingFK.boxOrigin 3 (2 * n))
    (hend :
      φ (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) p.val) =
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
          (boxVertStrictSectorPredecessor3 p.val p.property.1 p.property.2)) :
    (doubledBoxOriginToInnerEndpointSource n p.val).map φ.toEmbedding =
      doubledBoxOriginToInnerEndpointSource n
        (boxVertStrictSectorPredecessor3 p.val p.property.1 p.property.2) :=
  doubledBoxOriginToInnerEndpointSource_map_eq_of_maps_origin_endpoint
    φ horigin hend

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpointSource_map_eq_diagonalPredecessor_of_maps_origin_endpoint
    {n : ℕ}
    (p :
      {v : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n v ∧
          boxVertTransverseHeight3 v ≠ 0 ∧
            ¬ ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))})
    (φ : FK.boxVerts 3 (2 * n) ≃ FK.boxVerts 3 (2 * n))
    (horigin :
      φ (IsingFK.boxOrigin 3 (2 * n)) =
        IsingFK.boxOrigin 3 (2 * n))
    (hend :
      φ (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) p.val) =
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
          (boxVertDiagonalPredecessor3 p.val p.property.1 p.property.2.1
            p.property.2.2)) :
    (doubledBoxOriginToInnerEndpointSource n p.val).map φ.toEmbedding =
      doubledBoxOriginToInnerEndpointSource n
        (boxVertDiagonalPredecessor3 p.val p.property.1 p.property.2.1
          p.property.2.2) :=
  doubledBoxOriginToInnerEndpointSource_map_eq_of_maps_origin_endpoint
    φ horigin hend

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpointSource_map_eq_strictSectorYPredecessor_of_maps_origin_endpoint
    {n : ℕ}
    (p :
      {v : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n v ∧
          ((v : Lattice.Site 3) (1 : Fin 3)) <
            ((v : Lattice.Site 3) (2 : Fin 3)) ∧
              0 < ((v : Lattice.Site 3) (1 : Fin 3))})
    (φ : FK.boxVerts 3 (2 * n) ≃ FK.boxVerts 3 (2 * n))
    (horigin :
      φ (IsingFK.boxOrigin 3 (2 * n)) =
        IsingFK.boxOrigin 3 (2 * n))
    (hend :
      φ (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) p.val) =
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
          (boxVertStrictSectorYPredecessor3 p.val p.property.1
            p.property.2.1 p.property.2.2)) :
    (doubledBoxOriginToInnerEndpointSource n p.val).map φ.toEmbedding =
      doubledBoxOriginToInnerEndpointSource n
        (boxVertStrictSectorYPredecessor3 p.val p.property.1
          p.property.2.1 p.property.2.2) :=
  doubledBoxOriginToInnerEndpointSource_map_eq_of_maps_origin_endpoint
    φ horigin hend


theorem expectationJ_doubledBoxOriginToInnerEndpointSource_eq_of_boxVertHasCoords3
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n} {x y z : ℤ}
    (hv : boxVertHasCoords3 v x y z)
    (hw : boxVertHasCoords3 w x y z) :
    Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n v) =
      Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n w) := by
  rw [doubledBoxOriginToInnerEndpointSource_eq_of_boxVertHasCoords3 hv hw]


theorem expectationJ_le_of_currentSum_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) {A B : Finset V}
    (hraw : Sharpness.currentSum G β J A ≤ Sharpness.currentSum G β J B) :
    Sharpness.expectationJ G β J A ≤ Sharpness.expectationJ G β J B := by
  rw [Sharpness.current_representation, Sharpness.current_representation]
  exact
    div_le_div_of_nonneg_right hraw
      (le_of_lt (currentSum_empty_pos G β J))


theorem currentSum_le_of_expectationJ_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) {A B : Finset V}
    (hJ : Sharpness.expectationJ G β J A ≤ Sharpness.expectationJ G β J B) :
    Sharpness.currentSum G β J A ≤ Sharpness.currentSum G β J B := by
  rw [Sharpness.current_representation, Sharpness.current_representation] at hJ
  have hZpos : 0 < Sharpness.currentSum G β J (∅ : Finset V) :=
    currentSum_empty_pos G β J
  have hmul := (div_le_iff₀ hZpos).mp hJ
  have hZne : Sharpness.currentSum G β J (∅ : Finset V) ≠ 0 :=
    ne_of_gt hZpos
  simpa [div_mul_cancel₀ _ hZne] using hmul


theorem expectationJ_le_iff_currentSum_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A B : Finset V) :
    Sharpness.expectationJ G β J A ≤ Sharpness.expectationJ G β J B ↔
      Sharpness.currentSum G β J A ≤ Sharpness.currentSum G β J B :=
  ⟨currentSum_le_of_expectationJ_le G β J,
    expectationJ_le_of_currentSum_le G β J⟩

set_option linter.style.longLine false in


theorem sourcePairSum_comm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A B : Finset V) :
    Sharpness.sourcePairSum G β J A B =
      Sharpness.sourcePairSum G β J B A := by
  rw [Sharpness.sourcePairSum_eq_mul, Sharpness.sourcePairSum_eq_mul]
  exact mul_comm _ _

set_option linter.style.longLine false in


theorem sourcePairSum_empty_add_sourcePairSum_le_sourcePairSum_empty_of_currentSum_product_split_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A B P : Finset V)
    (hcurrent :
      Sharpness.currentSum G β J A *
          Sharpness.currentSum G β J (∅ : Finset V) +
        Sharpness.currentSum G β J B *
          Sharpness.currentSum G β J P ≤
        Sharpness.currentSum G β J B *
          Sharpness.currentSum G β J (∅ : Finset V)) :
    Sharpness.sourcePairSum G β J A (∅ : Finset V) +
        Sharpness.sourcePairSum G β J B P ≤
      Sharpness.sourcePairSum G β J B (∅ : Finset V) := by
  simpa [Sharpness.sourcePairSum_eq_mul] using hcurrent

set_option linter.style.longLine false in


theorem sourcePairSum_empty_add_sourcePairSum_le_sourcePairSum_empty_of_currentSum_expectationJ_split_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A B P : Finset V)
    (hcurrentJ :
      Sharpness.currentSum G β J A +
          Sharpness.currentSum G β J B *
            Sharpness.expectationJ G β J P ≤
        Sharpness.currentSum G β J B) :
    Sharpness.sourcePairSum G β J A (∅ : Finset V) +
        Sharpness.sourcePairSum G β J B P ≤
      Sharpness.sourcePairSum G β J B (∅ : Finset V) := by
  rw [Sharpness.current_representation] at hcurrentJ
  let Z : ℝ := Sharpness.currentSum G β J (∅ : Finset V)
  let CA : ℝ := Sharpness.currentSum G β J A
  let CB : ℝ := Sharpness.currentSum G β J B
  let CP : ℝ := Sharpness.currentSum G β J P
  have hZpos : 0 < Z := by
    simpa [Z] using currentSum_empty_pos G β J
  have hZne : Z ≠ 0 := ne_of_gt hZpos
  have hmul :=
    mul_le_mul_of_nonneg_right
      (show CA + CB * (CP / Z) ≤ CB by
        simpa [CA, CB, CP, Z] using hcurrentJ)
      (le_of_lt hZpos)
  have hproduct : CA * Z + CB * CP ≤ CB * Z := by
    calc
      CA * Z + CB * CP = (CA + CB * (CP / Z)) * Z := by
        rw [add_mul, mul_assoc, div_mul_cancel₀ CP hZne]
      _ ≤ CB * Z := hmul
  exact
    sourcePairSum_empty_add_sourcePairSum_le_sourcePairSum_empty_of_currentSum_product_split_le
      G β J A B P (by simpa [CA, CB, CP, Z] using hproduct)

set_option linter.style.longLine false in


theorem sourcePairSum_empty_add_sourcePairSum_le_sourcePairSum_empty_of_expectationJ_split_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A B P : Finset V)
    (hJ :
      Sharpness.expectationJ G β J A +
          Sharpness.expectationJ G β J B *
            Sharpness.expectationJ G β J P ≤
        Sharpness.expectationJ G β J B) :
    Sharpness.sourcePairSum G β J A (∅ : Finset V) +
        Sharpness.sourcePairSum G β J B P ≤
      Sharpness.sourcePairSum G β J B (∅ : Finset V) := by
  let Z : ℝ := Sharpness.currentSum G β J (∅ : Finset V)
  let CA : ℝ := Sharpness.currentSum G β J A
  let CB : ℝ := Sharpness.currentSum G β J B
  let EA : ℝ := Sharpness.expectationJ G β J A
  let EB : ℝ := Sharpness.expectationJ G β J B
  let EP : ℝ := Sharpness.expectationJ G β J P
  have hZpos : 0 < Z := by
    simpa [Z] using currentSum_empty_pos G β J
  have hZne : Z ≠ 0 := ne_of_gt hZpos
  have hAZ : EA * Z = CA := by
    simp [EA, CA, Z, Sharpness.current_representation, hZne]
  have hBZ : EB * Z = CB := by
    simp [EB, CB, Z, Sharpness.current_representation, hZne]
  have hmul :
      (EA + EB * EP) * Z ≤ EB * Z :=
    mul_le_mul_of_nonneg_right
      (by simpa [EA, EB, EP] using hJ) hZpos.le
  have hcurrentJ : CA + CB * EP ≤ CB := by
    calc
      CA + CB * EP = (EA + EB * EP) * Z := by
        calc
          CA + CB * EP = EA * Z + (EB * Z) * EP := by rw [hAZ, hBZ]
          _ = (EA + EB * EP) * Z := by ring
      _ ≤ EB * Z := hmul
      _ = CB := hBZ
  exact
    sourcePairSum_empty_add_sourcePairSum_le_sourcePairSum_empty_of_currentSum_expectationJ_split_le
      G β J A B P (by simpa [CA, CB, EP] using hcurrentJ)

set_option linter.style.longLine false in


theorem expectationJ_split_le_of_ratio_add_le_one
    {EA EB EP : ℝ} (hBpos : 0 < EB)
    (hratio : EA / EB + EP ≤ 1) :
    EA + EB * EP ≤ EB := by
  have hBnonneg : 0 ≤ EB := le_of_lt hBpos
  have hBne : EB ≠ 0 := ne_of_gt hBpos
  have hmul := mul_le_mul_of_nonneg_right hratio hBnonneg
  calc
    EA + EB * EP = (EA / EB + EP) * EB := by
      field_simp [hBne]
    _ ≤ 1 * EB := hmul
    _ = EB := by ring

set_option linter.style.longLine false in

theorem ratio_add_le_one_of_expectationJ_split_le
    {EA EB EP : ℝ} (hBpos : 0 < EB)
    (hsplit : EA + EB * EP ≤ EB) :
    EA / EB + EP ≤ 1 := by
  have hBnonneg : 0 ≤ EB := le_of_lt hBpos
  have hBne : EB ≠ 0 := ne_of_gt hBpos
  have hdiv := div_le_div_of_nonneg_right hsplit hBnonneg
  calc
    EA / EB + EP = (EA + EB * EP) / EB := by
      field_simp [hBne]
    _ ≤ EB / EB := hdiv
    _ = 1 := by field_simp [hBne]

set_option linter.style.longLine false in


theorem expectationJ_split_le_iff_ratio_add_le_one
    {EA EB EP : ℝ} (hBpos : 0 < EB) :
    EA + EB * EP ≤ EB ↔ EA / EB + EP ≤ 1 :=
  ⟨ratio_add_le_one_of_expectationJ_split_le hBpos,
    expectationJ_split_le_of_ratio_add_le_one hBpos⟩


theorem edgeCopySourcePairEmptyCollapsedSum_eq_tsum_term
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) :
    edgeCopySourcePairEmptyCollapsedSum G β J A =
      ∑' m : ↥G.edgeFinset → ℕ,
        edgeCopySourcePairEmptyCollapsedTerm G β J A m := rfl


theorem edgeCopySourcePairEmptyCollapsedTerm_summable
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) :
    Summable (fun m : ↥G.edgeFinset → ℕ =>
      edgeCopySourcePairEmptyCollapsedTerm G β J A m) := by
  simpa [edgeCopySourcePairEmptyCollapsedTerm,
    edgeCopySourcePairEmptyCollapsedMultiplicity, edgeCopySourceSector] using
    edgeCopySourcePairEmptyCollapsedSummand_summable G β J A


theorem edgeCopySourcePairEmptyCollapsedTerm_eq_multiplicity_mul_weight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V)
    (m : ↥G.edgeFinset → ℕ) :
    edgeCopySourcePairEmptyCollapsedTerm G β J A m =
      edgeCopySourcePairEmptyCollapsedMultiplicity G A m *
        Sharpness.weight G β J (Sharpness.ofEdgeFun G m) := rfl

end Exact3D
end StatMech

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ComponentThirdSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCombinatorics
import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part19
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex_inactive_image_source_ne_twoPoint
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    {D : finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v}
    (hD : D ∈
      (finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex
        (Ω.filter (fun m => ¬ finiteBoundaryGhostFullSourceOnePoint n m))
        v).image) :
    D.1 ≠
      (({some (IsingFK.boxOrigin 3 n)} :
        Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) := by
  classical
  let I :=
    finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex
      (Ω.filter (fun m => ¬ finiteBoundaryGhostFullSourceOnePoint n m)) v
  rcases (FinsetFiberIndex.mem_image I D).mp (by simpa [I] using hD) with
    ⟨a, ha_domain, hmap⟩
  have hinactive : ¬ finiteBoundaryGhostFullSourceOnePoint n a.1 := by
    have haΩ :
        a.1 ∈ Ω.filter
          (fun m => ¬ finiteBoundaryGhostFullSourceOnePoint n m) := by
      exact
        (finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport_mem
          (Ω.filter (fun m => ¬ finiteBoundaryGhostFullSourceOnePoint n m))
          v a).mp (by
            simpa [I, finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex]
              using ha_domain)
    exact (Finset.mem_filter.mp haΩ).2
  have hclass :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (Sharpness.withGhost (FK.boxGraph 3 n)) a.1)
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
            (Sharpness.withGhost (FK.boxGraph 3 n)) a.1)) ∆
          ({some v, none} : Finset (Option (FK.boxVerts 3 n))) =
        D.1 := by
    simpa [I, finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex]
      using congrArg Sigma.fst hmap
  intro hDclass
  exact
    finiteBoundaryGhostDecrementedSourceWeightVertexSigma_inactive_fullSourceClass_ne_twoPoint
      a hinactive (hclass.trans hDclass)

set_option linter.style.longLine false in


theorem
    finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex_inactive_image_filter_twoPoint_eq_empty
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    ((finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex
        (Ω.filter (fun m => ¬ finiteBoundaryGhostFullSourceOnePoint n m))
        v).image.filter
      (fun D : finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v =>
        D.1 =
          (({some (IsingFK.boxOrigin 3 n)} :
            Finset (Option (FK.boxVerts 3 n))) ∆ {some v}))) =
      ∅ := by
  classical
  ext D
  constructor
  · intro hD
    rcases Finset.mem_filter.mp hD with ⟨hDimage, hDclass⟩
    exact False.elim
      (finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex_inactive_image_source_ne_twoPoint
        Ω v hDimage hDclass)
  · intro hD
    simp at hD

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveClassifiedCoefficientWeightSum_eq_nonTwoPointClassFilter
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    finiteBoundaryGhostSourceInactiveClassifiedCoefficientWeightSum
        β H n Ω v =
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
        β H n Ω v := by
  classical
  let I :=
    finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex
      (Ω.filter (fun m => ¬ finiteBoundaryGhostFullSourceOnePoint n m)) v
  have hfilter :
      I.image.filter
          (fun D : finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v =>
            D.1 ≠
              (({some (IsingFK.boxOrigin 3 n)} :
                Finset (Option (FK.boxVerts 3 n))) ∆ {some v})) =
        I.image := by
    ext D
    constructor
    · intro hD
      exact (Finset.mem_filter.mp hD).1
    · intro hD
      exact Finset.mem_filter.mpr
        ⟨hD,
          finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex_inactive_image_source_ne_twoPoint
            Ω v (by simpa [I] using hD)⟩
  simp [finiteBoundaryGhostSourceInactiveClassifiedCoefficientWeightSum, I,
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum,
    hfilter]

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum_nonneg
    {β H : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    0 ≤
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
        β H n Ω v := by
  classical
  dsimp [finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum]
  refine Finset.sum_nonneg ?_
  intro D _hD
  exact
    mul_nonneg (Nat.cast_nonneg _)
      (finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceDataWeight_nonneg
        hβ hH D)

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum_filter_add_filter_not
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (P : finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
      Prop)
    [DecidablePred P] :
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
        β H n Ω v =
      (∑ D ∈
          (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSupport
            n Ω v).filter P,
          finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H D) +
        ∑ D ∈
          (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSupport
            n Ω v).filter (fun D => ¬ P D),
          finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H D := by
  classical
  rw [
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum_eq_support_sum]
  exact
    (Finset.sum_filter_add_sum_filter_not
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSupport
        n Ω v)
      P
      (finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H)).symm

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum_le_of_filter_le_filter_not_le
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (P : finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
      Prop)
    [DecidablePred P]
    {A B C : ℝ}
    (hP :
      (∑ D ∈
          (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSupport
            n Ω v).filter P,
          finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H D) ≤
        A)
    (hnot :
      (∑ D ∈
          (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSupport
            n Ω v).filter (fun D => ¬ P D),
          finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H D) ≤
        B)
    (hAB : A + B ≤ C) :
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
        β H n Ω v ≤ C := by
  calc
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
        β H n Ω v =
      (∑ D ∈
          (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSupport
            n Ω v).filter P,
          finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H D) +
        ∑ D ∈
          (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSupport
            n Ω v).filter (fun D => ¬ P D),
          finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H D :=
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum_filter_add_filter_not
        β H n Ω v P
    _ ≤ A + B := add_le_add hP hnot
    _ ≤ C := hAB

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum_eq_label_sum
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (label :
      finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v → ι) :
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
        β H n Ω v =
      ∑ i : ι,
        ∑ D ∈
          (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSupport
            n Ω v).filter (fun D => label D = i),
          finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H D := by
  classical
  rw [
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum_eq_support_sum]
  rw [← Finset.sum_fiberwise_of_maps_to
    (s :=
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSupport
        n Ω v)
    (t := (Finset.univ : Finset ι)) (g := label)
    (fun D _hD => Finset.mem_univ (label D))
    (fun D => finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H D)]

set_option linter.style.longLine false in

theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum_le_of_label_sum_le
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (label :
      finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v → ι)
    {A : ι → ℝ} {C : ℝ}
    (hcase :
      ∀ i,
        (∑ D ∈
          (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSupport
            n Ω v).filter (fun D => label D = i),
          finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H D) ≤
          A i)
    (hC : (∑ i, A i) ≤ C) :
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
        β H n Ω v ≤ C := by
  calc
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
        β H n Ω v =
      ∑ i : ι,
        ∑ D ∈
          (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSupport
            n Ω v).filter (fun D => label D = i),
          finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H D :=
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum_eq_label_sum
        β H n Ω v label
    _ ≤ ∑ i, A i :=
      Finset.sum_le_sum (fun i _hi => hcase i)
    _ ≤ C := hC

set_option linter.style.longLine false in

theorem
    finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceInactiveRemainder_le_sourceInactiveClassifiedCoefficientWeightSum
    {β H : ℝ} (n : ℕ)
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceInactiveRemainder
        β H n Ω v ≤
      finiteBoundaryGhostSourceInactiveClassifiedCoefficientWeightSum
        β H n Ω v := by
  simpa [finiteBoundaryGhostSourceInactiveClassifiedCoefficientWeightSum] using
    finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceInactiveRemainder_le_fullSourceClassifiedVertexCurrentSupportDecrementedBoundaryGhostMultiplicity_succ_weight_sum
      (n := n) (β := β) (H := H) hβ hH Ω v

end Exact3D
end StatMech

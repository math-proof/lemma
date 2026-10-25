/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteIsingFKBridge.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.SurfaceTensionConvexity
import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
import Theorem.StatisticalMechanics.Code.FK.RotationInvariance.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.IsingBoxEncoding.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneProps.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.SimonLiebFull.Part2
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part46
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem finiteBoundaryGhostWeightNonzeroCutoff_mem
    {β H : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ} :
    m ∈ finiteBoundaryGhostWeightNonzeroCutoff β H n Ω ↔
      m ∈ Ω ∧
        Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) ≠
            0 := by
  classical
  simp [finiteBoundaryGhostWeightNonzeroCutoff]


theorem finiteBoundaryGhostWeightNonzeroCutoff_weight_ne_zero
    {β H : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
    (hm : m ∈ finiteBoundaryGhostWeightNonzeroCutoff β H n Ω) :
    Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
      (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
      (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) ≠
        0 :=
  (finiteBoundaryGhostWeightNonzeroCutoff_mem.mp hm).2


theorem finiteBoundaryGhostWeightNonzeroCutoff_subset
    {β H : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)} :
    finiteBoundaryGhostWeightNonzeroCutoff β H n Ω ⊆ Ω := by
  intro m hm
  exact (finiteBoundaryGhostWeightNonzeroCutoff_mem.mp hm).1


theorem finiteBoundaryGhostWeightNonzeroCutoff_mono
    {β H : ℝ} {n : ℕ}
    {Ω Ω' : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    (hΩ : Ω ⊆ Ω') :
    finiteBoundaryGhostWeightNonzeroCutoff β H n Ω ⊆
      finiteBoundaryGhostWeightNonzeroCutoff β H n Ω' := by
  intro m hm
  have hmΩ : m ∈ Ω :=
    (finiteBoundaryGhostWeightNonzeroCutoff_mem.mp hm).1
  have hne :
      Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) ≠
          0 :=
    finiteBoundaryGhostWeightNonzeroCutoff_weight_ne_zero hm
  exact finiteBoundaryGhostWeightNonzeroCutoff_mem.mpr
    ⟨hΩ hmΩ, hne⟩


theorem finiteBoundaryGhostWeightNonzeroCutoff_filter_eq
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (P :
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) → Prop)
    [DecidablePred P] :
    finiteBoundaryGhostWeightNonzeroCutoff β H n (Ω.filter P) =
      (finiteBoundaryGhostWeightNonzeroCutoff β H n Ω).filter P := by
  classical
  ext m
  constructor
  · intro hm
    have hmfilter :
        m ∈ Ω.filter P :=
      (finiteBoundaryGhostWeightNonzeroCutoff_mem.mp hm).1
    have hΩP : m ∈ Ω ∧ P m := Finset.mem_filter.mp hmfilter
    have hne :
        Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) ≠
            0 :=
      (finiteBoundaryGhostWeightNonzeroCutoff_mem.mp hm).2
    exact Finset.mem_filter.mpr
      ⟨finiteBoundaryGhostWeightNonzeroCutoff_mem.mpr ⟨hΩP.1, hne⟩,
        hΩP.2⟩
  · intro hm
    have hmnzP :
        m ∈ finiteBoundaryGhostWeightNonzeroCutoff β H n Ω ∧ P m :=
      Finset.mem_filter.mp hm
    have hΩne :
        m ∈ Ω ∧
          Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
            (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
            (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) ≠
              0 :=
      finiteBoundaryGhostWeightNonzeroCutoff_mem.mp hmnzP.1
    exact finiteBoundaryGhostWeightNonzeroCutoff_mem.mpr
      ⟨Finset.mem_filter.mpr ⟨hΩne.1, hmnzP.2⟩, hΩne.2⟩


theorem finiteBoundaryGhostWeightNonzeroCutoff_idem
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    finiteBoundaryGhostWeightNonzeroCutoff β H n
        (finiteBoundaryGhostWeightNonzeroCutoff β H n Ω) =
      finiteBoundaryGhostWeightNonzeroCutoff β H n Ω := by
  classical
  ext m
  constructor
  · intro hm
    exact finiteBoundaryGhostWeightNonzeroCutoff_subset hm
  · intro hm
    exact finiteBoundaryGhostWeightNonzeroCutoff_mem.mpr
      ⟨hm, finiteBoundaryGhostWeightNonzeroCutoff_weight_ne_zero hm⟩


theorem finiteBoundaryGhostCollapsedSourceSummand_eq_zero_of_weight_eq_zero
    {β H : ℝ} {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (hweight :
      Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) =
          0) :
    finiteBoundaryGhostCollapsedSourceSummand β H n m = 0 := by
  simp [finiteBoundaryGhostCollapsedSourceSummand, hweight]


theorem finiteBoundaryGhostCollapsedSourceSummand_finset_sum_eq_weightNonzeroCutoff
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) =
      ∑ m ∈ finiteBoundaryGhostWeightNonzeroCutoff β H n Ω,
        finiteBoundaryGhostCollapsedSourceSummand β H n m := by
  classical
  unfold finiteBoundaryGhostWeightNonzeroCutoff
  calc
    (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) =
        ∑ m ∈ Ω,
          if Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
              (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
              (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m)
                ≠ 0 then
            finiteBoundaryGhostCollapsedSourceSummand β H n m
          else
            0 := by
      refine Finset.sum_congr rfl ?_
      intro m _hm
      by_cases hweight :
          Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
            (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
            (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) ≠
              0
      · simp [hweight]
      · have hzero :
            Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
              (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
              (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) =
                0 := by
          exact not_not.mp hweight
        simp [hweight,
          finiteBoundaryGhostCollapsedSourceSummand_eq_zero_of_weight_eq_zero
            (β := β) (H := H) (n := n) m hzero]
    _ =
        ∑ m ∈ Ω.filter
          (fun m =>
            Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
              (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
              (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n))
                m) ≠ 0),
          finiteBoundaryGhostCollapsedSourceSummand β H n m := by
      rw [Finset.sum_filter]


end Exact3D
end StatMech

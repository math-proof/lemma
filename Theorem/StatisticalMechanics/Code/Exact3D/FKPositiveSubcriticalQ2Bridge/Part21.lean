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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part23
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

@[simp] theorem none_not_mem_finiteBoundaryGhostOriginalSet
    (d n : ℕ) :
    none ∉ finiteBoundaryGhostOriginalSet d n := by
  classical
  simp [finiteBoundaryGhostOriginalSet]

@[simp] theorem some_mem_finiteBoundaryGhostOriginalSet
    (d n : ℕ) (x : FK.boxVerts d n) :
    some x ∈ finiteBoundaryGhostOriginalSet d n := by
  classical
  simp [finiteBoundaryGhostOriginalSet]

@[simp] theorem finiteBoundaryGhostOnePointSource_card
    (d n : ℕ) :
    (finiteBoundaryGhostOnePointSource d n).card = 2 := by
  simp [finiteBoundaryGhostOnePointSource]

@[simp] theorem finiteBoundaryGhostOnePointSource_eq_symmDiff
    (d n : ℕ) :
    finiteBoundaryGhostOnePointSource d n =
      (({some (IsingFK.boxOrigin d n)} :
          Finset (Option (FK.boxVerts d n))) ∆ {none}) := by
  classical
  ext x
  rcases x with _ | v <;>
    simp [finiteBoundaryGhostOnePointSource, Finset.mem_symmDiff]


theorem finiteBoundaryGhost_sourceSector_connK_origin_none
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (K : Finset (Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) m))
    (hsrc :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) m) K =
        finiteBoundaryGhostOnePointSource 3 n) :
    Sharpness.RandomCurrent.connK
      (Sharpness.FluxEdgeCopy.endsM
        (Sharpness.withGhost (FK.boxGraph 3 n)) m) K
      (some (IsingFK.boxOrigin 3 n)) none := by
  classical
  let ends :=
    Sharpness.FluxEdgeCopy.endsM
      (Sharpness.withGhost (FK.boxGraph 3 n)) m
  have huodd :
      Odd (Sharpness.RandomCurrent.degK ends K
        (some (IsingFK.boxOrigin 3 n))) := by
    rw [← Sharpness.RandomCurrent.mem_sources]
    rw [hsrc]
    simp [finiteBoundaryGhostOnePointSource]
  have hbdry :
      ∀ x, Odd (Sharpness.RandomCurrent.degK ends K x) →
        x = some (IsingFK.boxOrigin 3 n) ∨ x = none := by
    intro x hx
    have hxmem : x ∈ Sharpness.RandomCurrent.sources ends K := by
      rw [Sharpness.RandomCurrent.mem_sources]
      exact hx
    rw [hsrc] at hxmem
    simpa [finiteBoundaryGhostOnePointSource] using hxmem
  exact
    Sharpness.RandomCurrent.path_exists ends K
      (fun i _hi =>
        Sharpness.FluxEdgeCopy.endsM_not_isDiag
          (Sharpness.withGhost (FK.boxGraph 3 n)) m i)
      (some (IsingFK.boxOrigin 3 n)) none huodd hbdry (by simp)


theorem finiteBoundaryGhost_sourceSector_has_ghostCrossingCopy
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (K : Finset (Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) m))
    (hsrc :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) m) K =
        finiteBoundaryGhostOnePointSource 3 n) :
    ∃ v : FK.boxVerts 3 n,
      (∃ i ∈ K,
        some v ∈ Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) m i ∧
        none ∈ Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) m i) ∧
      Sharpness.RandomCurrent.connK
        (Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) m) K
        (some (IsingFK.boxOrigin 3 n)) (some v) := by
  classical
  let ends :=
    Sharpness.FluxEdgeCopy.endsM
      (Sharpness.withGhost (FK.boxGraph 3 n)) m
  have hconn :
      Sharpness.RandomCurrent.connK ends K
        (some (IsingFK.boxOrigin 3 n)) none :=
    finiteBoundaryGhost_sourceSector_connK_origin_none m K hsrc
  obtain ⟨x, y, hx, hy, hadj, hpre⟩ :=
    randomCurrent_connK_firstExit_adjStep ends K
      (finiteBoundaryGhostOriginalSet 3 n) hconn
      (some_mem_finiteBoundaryGhostOriginalSet 3 n
        (IsingFK.boxOrigin 3 n))
      (none_not_mem_finiteBoundaryGhostOriginalSet 3 n)
  rcases x with _ | v
  · exact False.elim (none_not_mem_finiteBoundaryGhostOriginalSet 3 n hx)
  · rcases y with _ | w
    · rcases hadj with ⟨i, hiK, hxedge, hyedge, _hne⟩
      exact ⟨v, ⟨i, hiK, hxedge, hyedge⟩, hpre⟩
    · exact False.elim (hy (some_mem_finiteBoundaryGhostOriginalSet 3 n w))


theorem finiteBoundaryGhost_sourceSector_has_boundaryGhostCrossingCopy
    {β H : ℝ} {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (K : Finset (Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) m))
    (hsrc :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) m) K =
        finiteBoundaryGhostOnePointSource 3 n)
    (hweight :
      Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) ≠ 0) :
    ∃ v : FK.boxVerts 3 n,
      FK.boxBoundary 3 n v ∧
      (∃ i ∈ K,
        some v ∈ Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) m i ∧
        none ∈ Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) m i) ∧
      Sharpness.RandomCurrent.connK
        (Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) m) K
        (some (IsingFK.boxOrigin 3 n)) (some v) := by
  classical
  obtain ⟨v, hcross, hconn⟩ :=
    finiteBoundaryGhost_sourceSector_has_ghostCrossingCopy m K hsrc
  refine ⟨v, ?_, hcross, hconn⟩
  by_contra hvnot
  obtain ⟨i, _hiK, hsome, hnone⟩ := hcross
  have hedge :
      Sharpness.FluxEdgeCopy.endsM
        (Sharpness.withGhost (FK.boxGraph 3 n)) m i =
          s(some v, none) := by
    exact (Sym2.mem_and_mem_iff (by simp)).mp ⟨hsome, hnone⟩
  have hmpos : 0 < m i.1 :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) i.2.2
  have hJedge :
      boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1) i.1.1 = 0 := by
    have hJends :
        boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
          (Sharpness.FluxEdgeCopy.endsM
            (Sharpness.withGhost (FK.boxGraph 3 n)) m i) = 0 := by
      rw [hedge]
      exact boundaryGhostCoupling_some_none_of_not_boundary
        (FK.boxBoundary 3 n) (fun _ => (1 : ℝ)) hvnot
    simpa [Sharpness.FluxEdgeCopy.endsM] using hJends
  exact hweight
    (weight_ofEdgeFun_eq_zero_of_edge_coupling_eq_zero
      (Sharpness.withGhost (FK.boxGraph 3 n)) β
      (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
      m i.1 hmpos hJedge)


end Exact3D
end StatMech

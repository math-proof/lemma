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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part69
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem
    finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies_transport_univ_source_onePoint
    {n : ℕ}
    (d : Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostCollapsedTwoPointSourceData n v))
    {i : Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) d.2.toSourceData.1}
    (hi : i ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies d) :
    Sharpness.RandomCurrent.sources
      (Sharpness.FluxEdgeCopy.endsM
        (Sharpness.withGhost (FK.boxGraph 3 n))
        (Function.update d.2.toSourceData.1 i.1
          (d.2.toSourceData.1 i.1 - 1)))
      (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
        (Sharpness.withGhost (FK.boxGraph 3 n))
        (Function.update d.2.toSourceData.1 i.1
          (d.2.toSourceData.1 i.1 - 1)))) =
      finiteBoundaryGhostOnePointSource 3 n := by
  classical
  have hpre :=
    finiteBoundaryGhost_sources_preimageErase_boundaryGhostCopy_from_twoPoint
      d.2.toSourceData.1
      (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
        (Sharpness.withGhost (FK.boxGraph 3 n)) d.2.toSourceData.1))
      (Finset.mem_univ i)
      (finiteBoundaryGhostCollapsedTwoPointSourceData_fullSource d.2)
      (finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies_ends d hi)
  simpa [copyDeletePreimageDecrementEraseFinset_univ] using hpre


theorem
    finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies_transport_complement_source
    {n : ℕ}
    (d : Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostCollapsedTwoPointSourceData n v))
    {i : Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) d.2.toSourceData.1}
    (hi : i ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies d) :
    let m' :=
      Function.update d.2.toSourceData.1 i.1
        (d.2.toSourceData.1 i.1 - 1)
    let K' :=
      copyDeletePreimageDecrementEraseFinset
        (Sharpness.withGhost (FK.boxGraph 3 n)) d.2.toSourceData.1 i
        d.2.toSourceData.2.1
    Sharpness.RandomCurrent.sources
      (Sharpness.FluxEdgeCopy.endsM
        (Sharpness.withGhost (FK.boxGraph 3 n)) m')
      ((Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
        (Sharpness.withGhost (FK.boxGraph 3 n)) m')) \ K') =
      (({some d.1} : Finset (Option (FK.boxVerts 3 n))) ∆ {none}) := by
  classical
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let m' :=
    Function.update d.2.toSourceData.1 i.1
      (d.2.toSourceData.1 i.1 - 1)
  let K' :=
    copyDeletePreimageDecrementEraseFinset
      (Sharpness.withGhost (FK.boxGraph 3 n)) d.2.toSourceData.1 i
      d.2.toSourceData.2.1
  let ends := Sharpness.FluxEdgeCopy.endsM G m'
  change
    Sharpness.RandomCurrent.sources ends
      ((Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m')) \ K') =
      (({some d.1} : Finset (Option (FK.boxVerts 3 n))) ∆ {none})
  have hitarget :
      i ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies d :=
    (Finset.mem_filter.mp hi).1
  have hcompl_set :
      ((Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m')) \ K') =
        ((Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m')) ∆ K') := by
    ext j
    simp only [Finset.mem_sdiff, Finset.mem_symmDiff, Finset.mem_univ,
      true_and]
    tauto
  rw [hcompl_set]
  rw [Sharpness.RandomCurrent.sources_symmDiff ends
    (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m')) K']
  have hfull :
      Sharpness.RandomCurrent.sources ends
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m')) =
        finiteBoundaryGhostOnePointSource 3 n := by
    simpa [G, m', ends] using
      finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies_transport_univ_source_onePoint
        d hitarget
  have hselected :
      Sharpness.RandomCurrent.sources ends K' =
        (({some (IsingFK.boxOrigin 3 n)} :
          Finset (Option (FK.boxVerts 3 n))) ∆ {some d.1}) := by
    simpa [G, m', K', ends] using
      finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies_transport_source
        d hi
  rw [hfull, hselected, finiteBoundaryGhostOnePointSource_eq_symmDiff]
  ext x
  rcases x with _ | w
  · simp [Finset.mem_symmDiff]
  · by_cases hwo : w = IsingFK.boxOrigin 3 n
    · subst w
      by_cases hov : IsingFK.boxOrigin 3 n = d.1
      · simp [Finset.mem_symmDiff, hov]
      · simp [Finset.mem_symmDiff, hov]
    · by_cases hwv : w = d.1
      · subst w
        have hvo : d.1 ≠ IsingFK.boxOrigin 3 n := by
          intro h
          exact hwo h
        simp [Finset.mem_symmDiff, hvo]
      · simp [Finset.mem_symmDiff, hwo, hwv]


theorem
    finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies_transport_complement_source
    {n : ℕ}
    (d : Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostCollapsedTwoPointSourceData n v))
    {i : Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) d.2.toSourceData.1}
    (hi : i ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies d) :
    let m' :=
      Function.update d.2.toSourceData.1 i.1
        (d.2.toSourceData.1 i.1 - 1)
    let K' :=
      copyDeletePreimageDecrementEraseFinset
        (Sharpness.withGhost (FK.boxGraph 3 n)) d.2.toSourceData.1 i
        d.2.toSourceData.2.1
    Sharpness.RandomCurrent.sources
      (Sharpness.FluxEdgeCopy.endsM
        (Sharpness.withGhost (FK.boxGraph 3 n)) m')
      ((Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
        (Sharpness.withGhost (FK.boxGraph 3 n)) m')) \ K') =
      (∅ : Finset (Option (FK.boxVerts 3 n))) := by
  classical
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let m' :=
    Function.update d.2.toSourceData.1 i.1
      (d.2.toSourceData.1 i.1 - 1)
  let K' :=
    copyDeletePreimageDecrementEraseFinset
      (Sharpness.withGhost (FK.boxGraph 3 n)) d.2.toSourceData.1 i
      d.2.toSourceData.2.1
  let ends := Sharpness.FluxEdgeCopy.endsM G m'
  change
    Sharpness.RandomCurrent.sources ends
      ((Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m')) \ K') =
      (∅ : Finset (Option (FK.boxVerts 3 n)))
  have hitarget :
      i ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies d :=
    (Finset.mem_filter.mp hi).1
  have hcompl_set :
      ((Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m')) \ K') =
        ((Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m')) ∆ K') := by
    ext j
    simp only [Finset.mem_sdiff, Finset.mem_symmDiff, Finset.mem_univ,
      true_and]
    tauto
  rw [hcompl_set]
  rw [Sharpness.RandomCurrent.sources_symmDiff ends
    (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m')) K']
  have hfull :
      Sharpness.RandomCurrent.sources ends
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m')) =
        finiteBoundaryGhostOnePointSource 3 n := by
    simpa [G, m', ends] using
      finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies_transport_univ_source_onePoint
        d hitarget
  have hselected :
      Sharpness.RandomCurrent.sources ends K' =
        finiteBoundaryGhostOnePointSource 3 n := by
    simpa [G, m', K', ends] using
      finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies_transport_source
        d hi
  rw [hfull, hselected]
  ext x
  simp [Finset.mem_symmDiff]


end Exact3D
end StatMech

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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part5
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in
theorem mem_edgeCopySourceSectorContainingBothCopies
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A : Finset V} {m : ↥G.edgeFinset → ℕ}
    {first second : Sharpness.FluxEdgeCopy.Copy G m}
    {K : Finset (Sharpness.FluxEdgeCopy.Copy G m)} :
    K ∈ edgeCopySourceSectorContainingBothCopies G A m first second ↔
      K ∈ edgeCopySourceSector G A m ∧ first ∈ K ∧ second ∈ K := by
  simp [edgeCopySourceSectorContainingBothCopies]

set_option linter.style.longLine false in
theorem edgeCopySourceSectorContainingBothCopies_nonempty_of_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A : Finset V} {m : ↥G.edgeFinset → ℕ}
    {first second : Sharpness.FluxEdgeCopy.Copy G m}
    {K : Finset (Sharpness.FluxEdgeCopy.Copy G m)}
    (hK : K ∈ edgeCopySourceSector G A m) (hfirst : first ∈ K)
    (hsecond : second ∈ K) :
    (edgeCopySourceSectorContainingBothCopies G A m first second).Nonempty := by
  exact
    ⟨K,
      (mem_edgeCopySourceSectorContainingBothCopies
        (G := G) (A := A) (m := m) (first := first)
        (second := second) (K := K)).mpr
        ⟨hK, hfirst, hsecond⟩⟩

set_option linter.style.longLine false in
theorem edgeCopySourceSectorContainingBothCopies_card_pos_of_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A : Finset V} {m : ↥G.edgeFinset → ℕ}
    {first second : Sharpness.FluxEdgeCopy.Copy G m}
    {K : Finset (Sharpness.FluxEdgeCopy.Copy G m)}
    (hK : K ∈ edgeCopySourceSector G A m) (hfirst : first ∈ K)
    (hsecond : second ∈ K) :
    0 <
      (edgeCopySourceSectorContainingBothCopies G A m first second).card :=
  Finset.Nonempty.card_pos
    (edgeCopySourceSectorContainingBothCopies_nonempty_of_mem hK hfirst
      hsecond)

set_option linter.style.longLine false in


theorem edgeCopySourceSectorContainingBothCopies_comm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ)
    (first second : Sharpness.FluxEdgeCopy.Copy G m) :
    edgeCopySourceSectorContainingBothCopies G A m first second =
      edgeCopySourceSectorContainingBothCopies G A m second first := by
  classical
  ext K
  simp [edgeCopySourceSectorContainingBothCopies, and_comm, and_assoc]

set_option linter.style.longLine false in


theorem edgeCopySourceSectorContainingBothCopies_card_comm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ)
    (first second : Sharpness.FluxEdgeCopy.Copy G m) :
    (edgeCopySourceSectorContainingBothCopies G A m first second).card =
      (edgeCopySourceSectorContainingBothCopies G A m second first).card := by
  rw [edgeCopySourceSectorContainingBothCopies_comm G A m first second]

end Exact3D
end StatMech

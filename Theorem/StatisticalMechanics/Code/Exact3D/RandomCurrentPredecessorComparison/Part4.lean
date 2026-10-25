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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part3
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

theorem mem_edgeCopySourceSectorContainingCopy
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A : Finset V} {m : ↥G.edgeFinset → ℕ}
    {i : Sharpness.FluxEdgeCopy.Copy G m}
    {K : Finset (Sharpness.FluxEdgeCopy.Copy G m)} :
    K ∈ edgeCopySourceSectorContainingCopy G A m i ↔
      K ∈ edgeCopySourceSector G A m ∧ i ∈ K := by
  simp [edgeCopySourceSectorContainingCopy]

theorem edgeCopySourceSectorContainingCopy_nonempty_of_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A : Finset V} {m : ↥G.edgeFinset → ℕ}
    {i : Sharpness.FluxEdgeCopy.Copy G m}
    {K : Finset (Sharpness.FluxEdgeCopy.Copy G m)}
    (hK : K ∈ edgeCopySourceSector G A m) (hi : i ∈ K) :
    (edgeCopySourceSectorContainingCopy G A m i).Nonempty := by
  exact
    ⟨K,
      (mem_edgeCopySourceSectorContainingCopy
        (G := G) (A := A) (m := m) (i := i) (K := K)).mpr
        ⟨hK, hi⟩⟩

theorem edgeCopySourceSectorContainingCopy_card_pos_of_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A : Finset V} {m : ↥G.edgeFinset → ℕ}
    {i : Sharpness.FluxEdgeCopy.Copy G m}
    {K : Finset (Sharpness.FluxEdgeCopy.Copy G m)}
    (hK : K ∈ edgeCopySourceSector G A m) (hi : i ∈ K) :
    0 < (edgeCopySourceSectorContainingCopy G A m i).card :=
  Finset.Nonempty.card_pos
    (edgeCopySourceSectorContainingCopy_nonempty_of_mem hK hi)

set_option linter.style.longLine false in


theorem edgeCopySourceSectorContainingCopy_not_nonempty_iff_forall_not_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A : Finset V} {m : ↥G.edgeFinset → ℕ}
    {i : Sharpness.FluxEdgeCopy.Copy G m} :
    (¬ (edgeCopySourceSectorContainingCopy G A m i).Nonempty) ↔
      ∀ K ∈ edgeCopySourceSector G A m, i ∉ K := by
  constructor
  · intro hno K hK hi
    exact hno (edgeCopySourceSectorContainingCopy_nonempty_of_mem hK hi)
  · intro havoid hnonempty
    rcases hnonempty with ⟨K, hKcontaining⟩
    rcases
        (mem_edgeCopySourceSectorContainingCopy
          (G := G) (A := A) (m := m) (i := i) (K := K)).mp
          hKcontaining with
      ⟨hK, hi⟩
    exact havoid K hK hi

end Exact3D
end StatMech

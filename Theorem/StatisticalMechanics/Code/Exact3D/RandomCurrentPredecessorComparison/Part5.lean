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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part4
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in
theorem mem_edgeCopySourceSectorExcludingCopy
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A : Finset V} {m : ↥G.edgeFinset → ℕ}
    {i : Sharpness.FluxEdgeCopy.Copy G m}
    {K : Finset (Sharpness.FluxEdgeCopy.Copy G m)} :
    K ∈ edgeCopySourceSectorExcludingCopy G A m i ↔
      K ∈ edgeCopySourceSector G A m ∧ i ∉ K := by
  simp [edgeCopySourceSectorExcludingCopy]

set_option linter.style.longLine false in


theorem edgeCopySourceSector_eq_excludingCopy_of_forall_not_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A : Finset V} {m : ↥G.edgeFinset → ℕ}
    {i : Sharpness.FluxEdgeCopy.Copy G m}
    (havoid : ∀ K ∈ edgeCopySourceSector G A m, i ∉ K) :
    edgeCopySourceSector G A m =
      edgeCopySourceSectorExcludingCopy G A m i := by
  apply Finset.ext
  intro K
  constructor
  · intro hK
    exact
      (mem_edgeCopySourceSectorExcludingCopy
        (G := G) (A := A) (m := m) (i := i) (K := K)).mpr
        ⟨hK, havoid K hK⟩
  · intro hK
    exact
      ((mem_edgeCopySourceSectorExcludingCopy
        (G := G) (A := A) (m := m) (i := i) (K := K)).mp hK).1

set_option linter.style.longLine false in
theorem edgeCopySourceSectorExcludingCopy_nonempty_of_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A : Finset V} {m : ↥G.edgeFinset → ℕ}
    {i : Sharpness.FluxEdgeCopy.Copy G m}
    {K : Finset (Sharpness.FluxEdgeCopy.Copy G m)}
    (hK : K ∈ edgeCopySourceSector G A m) (hi : i ∉ K) :
    (edgeCopySourceSectorExcludingCopy G A m i).Nonempty := by
  exact
    ⟨K,
      (mem_edgeCopySourceSectorExcludingCopy
        (G := G) (A := A) (m := m) (i := i) (K := K)).mpr
        ⟨hK, hi⟩⟩

set_option linter.style.longLine false in
theorem edgeCopySourceSectorExcludingCopy_card_pos_of_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A : Finset V} {m : ↥G.edgeFinset → ℕ}
    {i : Sharpness.FluxEdgeCopy.Copy G m}
    {K : Finset (Sharpness.FluxEdgeCopy.Copy G m)}
    (hK : K ∈ edgeCopySourceSector G A m) (hi : i ∉ K) :
    0 < (edgeCopySourceSectorExcludingCopy G A m i).card :=
  Finset.Nonempty.card_pos
    (edgeCopySourceSectorExcludingCopy_nonempty_of_mem hK hi)

end Exact3D
end StatMech

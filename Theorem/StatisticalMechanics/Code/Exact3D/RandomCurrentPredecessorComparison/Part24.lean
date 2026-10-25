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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part22
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

theorem edgeCopyIncrementMap_fst
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (i : Sharpness.FluxEdgeCopy.Copy G m) :
    (edgeCopyIncrementMap G m e0 i).1 = i.1 := by
  classical
  rcases i with ⟨e, k⟩
  by_cases he : e = e0
  · subst e
    simp [edgeCopyIncrementMap]
  · simp [edgeCopyIncrementMap, he]


theorem edgeCopyIncrementMap_ends
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (i : Sharpness.FluxEdgeCopy.Copy G m) :
    Sharpness.FluxEdgeCopy.endsM G (Function.update m e0 (m e0 + 1))
        (edgeCopyIncrementMap G m e0 i) =
      Sharpness.FluxEdgeCopy.endsM G m i := by
  simpa [Sharpness.FluxEdgeCopy.endsM] using
    edgeCopyIncrementMap_fst G m e0 i


theorem edgeCopyIncrementInserted_ends
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset) :
    Sharpness.FluxEdgeCopy.endsM G (Function.update m e0 (m e0 + 1))
        (edgeCopyIncrementInserted G m e0) = e0.1 := by
  rfl

set_option linter.style.longLine false in


theorem edgeCopy_eq_incrementInserted_of_edge_eq_of_index_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    {i : Sharpness.FluxEdgeCopy.Copy G
      (Function.update m e0 (m e0 + 1))}
    (hedge : i.1 = e0) (hidx : (i.2 : ℕ) = m e0) :
    i = edgeCopyIncrementInserted G m e0 := by
  rcases i with ⟨e, k⟩
  dsimp at hedge hidx
  subst e
  have hk :
      k =
        (⟨m e0, by rw [Function.update_self]; omega⟩ :
          Fin (Function.update m e0 (m e0 + 1) e0)) := by
    apply Fin.ext
    exact hidx
  simp [edgeCopyIncrementInserted, hk]

set_option linter.style.longLine false in


theorem edgeCopySourceSectorSelectedEdgeCopyPairs_selectedCopy_eq_incrementInserted_of_update_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (hmzero : m e0 = 0)
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G
        (Function.update m e0 (m e0 + 1))) =>
      Sharpness.FluxEdgeCopy.Copy G (Function.update m e0 (m e0 + 1)))}
    (hp :
      p ∈ edgeCopySourceSectorSelectedEdgeCopyPairs G A
        (Function.update m e0 (m e0 + 1)) e0) :
    p.2 = edgeCopyIncrementInserted G m e0 := by
  simpa [edgeCopyIncrementInserted, hmzero] using
    edgeCopySourceSectorSelectedEdgeCopyPairs_selectedCopy_eq_inserted_of_update_zero
      G A m e0 hmzero hp

set_option linter.style.longLine false in


theorem edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_selectedCopy_eq_incrementInserted_of_update_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (hmzero : m e0 = 0)
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G
        (Function.update m e0 (m e0 + 1))) =>
      Sharpness.FluxEdgeCopy.Copy G (Function.update m e0 (m e0 + 1)))}
    (hp :
      p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A
        (Function.update m e0 (m e0 + 1)) e0) :
    p.2 = edgeCopyIncrementInserted G m e0 := by
  simpa [edgeCopyIncrementInserted, hmzero] using
    edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_selectedCopy_eq_inserted_of_update_zero
      G A m e0 hmzero hp

set_option linter.style.longLine false in


theorem edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_incrementInserted_mem_of_update_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (hmzero : m e0 = 0)
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G
        (Function.update m e0 (m e0 + 1))) =>
      Sharpness.FluxEdgeCopy.Copy G (Function.update m e0 (m e0 + 1)))}
    (hp :
      p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A
        (Function.update m e0 (m e0 + 1)) e0) :
    edgeCopyIncrementInserted G m e0 ∈ p.1 := by
  simpa [edgeCopyIncrementInserted, hmzero] using
    edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_inserted_mem_of_update_zero
      G A m e0 hmzero hp

set_option linter.style.longLine false in


theorem edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_selectedCopy_eq_incrementInserted_of_update_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (hmzero : m e0 = 0)
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G
        (Function.update m e0 (m e0 + 1))) =>
      Sharpness.FluxEdgeCopy.Copy G (Function.update m e0 (m e0 + 1)))}
    (hp :
      p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A
        (Function.update m e0 (m e0 + 1)) e0) :
    p.2 = edgeCopyIncrementInserted G m e0 := by
  exact
    edgeCopySourceSectorSelectedEdgeCopyPairs_selectedCopy_eq_incrementInserted_of_update_zero
      G A m e0 hmzero
      ((edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_mem
        G A (Function.update m e0 (m e0 + 1)) e0 p).mp hp |>.1)

set_option linter.style.longLine false in


theorem edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_incrementInserted_not_mem_of_update_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (hmzero : m e0 = 0)
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G
        (Function.update m e0 (m e0 + 1))) =>
      Sharpness.FluxEdgeCopy.Copy G (Function.update m e0 (m e0 + 1)))}
    (hp :
      p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A
        (Function.update m e0 (m e0 + 1)) e0) :
    edgeCopyIncrementInserted G m e0 ∉ p.1 := by
  classical
  have hpbranch :=
    (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_mem
      G A (Function.update m e0 (m e0 + 1)) e0 p).mp hp
  have hsel :
      p.2 = edgeCopyIncrementInserted G m e0 :=
    edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_selectedCopy_eq_incrementInserted_of_update_zero
      G A m e0 hmzero hp
  simpa [hsel] using hpbranch.2

set_option linter.style.longLine false in


theorem edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_fst_mem_excluding_incrementInserted_of_update_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (hmzero : m e0 = 0)
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G
        (Function.update m e0 (m e0 + 1))) =>
      Sharpness.FluxEdgeCopy.Copy G (Function.update m e0 (m e0 + 1)))}
    (hp :
      p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A
        (Function.update m e0 (m e0 + 1)) e0) :
    p.1 ∈
      edgeCopySourceSectorExcludingCopy G A
        (Function.update m e0 (m e0 + 1))
        (edgeCopyIncrementInserted G m e0) := by
  classical
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  have hpbranch :=
    (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_mem
      G A M e0 p).mp hp
  have hK : p.1 ∈ edgeCopySourceSector G A M :=
    (edgeCopySourceSectorSelectedEdgeCopyPairs_mem
      (G := G) (A := A) (m := M) (e0 := e0) (p := p)).mp
      hpbranch.1 |>.1
  have hnot : edgeCopyIncrementInserted G m e0 ∉ p.1 :=
    edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_incrementInserted_not_mem_of_update_zero
      G A m e0 hmzero hp
  exact
    (mem_edgeCopySourceSectorExcludingCopy
      (G := G) (A := A) (m := M)
      (i := edgeCopyIncrementInserted G m e0) (K := p.1)).mpr
      ⟨hK, hnot⟩

set_option linter.style.longLine false in


theorem edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_fst_mem_containing_owner_excluding_incrementInserted_of_update_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (hmzero : m e0 = 0)
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G
        (Function.update m e0 (m e0 + 1))) =>
      Sharpness.FluxEdgeCopy.Copy G (Function.update m e0 (m e0 + 1)))}
    (hp :
      p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A
        (Function.update m e0 (m e0 + 1)) e0)
    {owner : Sharpness.FluxEdgeCopy.Copy G
      (Function.update m e0 (m e0 + 1))}
    (howner : owner ∈ p.1) :
    p.1 ∈
      edgeCopySourceSectorContainingAndExcludingCopy G A
        (Function.update m e0 (m e0 + 1)) owner
        (edgeCopyIncrementInserted G m e0) := by
  classical
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  have hpbranch :=
    (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_mem
      G A M e0 p).mp hp
  have hK : p.1 ∈ edgeCopySourceSector G A M :=
    (edgeCopySourceSectorSelectedEdgeCopyPairs_mem
      (G := G) (A := A) (m := M) (e0 := e0) (p := p)).mp
      hpbranch.1 |>.1
  have hnot : edgeCopyIncrementInserted G m e0 ∉ p.1 :=
    edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_incrementInserted_not_mem_of_update_zero
      G A m e0 hmzero hp
  exact
    (mem_edgeCopySourceSectorContainingAndExcludingCopy
      (G := G) (A := A) (m := M) (inside := owner)
      (outside := edgeCopyIncrementInserted G m e0) (K := p.1)).mpr
      ⟨hK, howner, hnot⟩

set_option linter.style.longLine false in


theorem edgeCopySourceSectorContaining_incrementInserted_excluding_owner_not_fst_selectedEdgeCopyPairsOutsideCurrent_of_update_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (hmzero : m e0 = 0)
    (owner : Sharpness.FluxEdgeCopy.Copy G
      (Function.update m e0 (m e0 + 1)))
    {K : Finset (Sharpness.FluxEdgeCopy.Copy G
      (Function.update m e0 (m e0 + 1)))}
    (hK :
      K ∈ edgeCopySourceSectorContainingAndExcludingCopy G A
        (Function.update m e0 (m e0 + 1))
        (edgeCopyIncrementInserted G m e0) owner) :
    ¬ ∃ p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G
          (Function.update m e0 (m e0 + 1))) =>
        Sharpness.FluxEdgeCopy.Copy G (Function.update m e0 (m e0 + 1))),
      p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A
        (Function.update m e0 (m e0 + 1)) e0 ∧ p.1 = K := by
  classical
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  have hinserted_mem :
      edgeCopyIncrementInserted G m e0 ∈ K :=
    (mem_edgeCopySourceSectorContainingAndExcludingCopy
      (G := G) (A := A) (m := M)
      (inside := edgeCopyIncrementInserted G m e0) (outside := owner)
      (K := K)).mp hK |>.2.1
  rintro ⟨p, hp, hpK⟩
  have hnot :
      edgeCopyIncrementInserted G m e0 ∉ p.1 :=
    edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_incrementInserted_not_mem_of_update_zero
      G A m e0 hmzero hp
  have hin : edgeCopyIncrementInserted G m e0 ∈ p.1 := by
    simpa [hpK] using hinserted_mem
  exact hnot hin

set_option linter.style.longLine false in


theorem edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_fst_mem_containing_incrementInserted_of_update_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (hmzero : m e0 = 0)
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G
        (Function.update m e0 (m e0 + 1))) =>
      Sharpness.FluxEdgeCopy.Copy G (Function.update m e0 (m e0 + 1)))}
    (hp :
      p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A
        (Function.update m e0 (m e0 + 1)) e0) :
    p.1 ∈
      edgeCopySourceSectorContainingCopy G A
        (Function.update m e0 (m e0 + 1))
        (edgeCopyIncrementInserted G m e0) := by
  classical
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  have hpbranch :=
    (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_mem G A M e0 p).mp hp
  have hK : p.1 ∈ edgeCopySourceSector G A M :=
    (edgeCopySourceSectorSelectedEdgeCopyPairs_mem
      (G := G) (A := A) (m := M) (e0 := e0) (p := p)).mp
      hpbranch.1 |>.1
  have hinserted : edgeCopyIncrementInserted G m e0 ∈ p.1 :=
    edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_incrementInserted_mem_of_update_zero
      G A m e0 hmzero hp
  exact
    (mem_edgeCopySourceSectorContainingCopy
      (G := G) (A := A) (m := M)
      (i := edgeCopyIncrementInserted G m e0) (K := p.1)).mpr
      ⟨hK, hinserted⟩

set_option linter.style.longLine false in


theorem edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_fst_mem_containing_owner_and_incrementInserted_of_update_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (hmzero : m e0 = 0)
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G
        (Function.update m e0 (m e0 + 1))) =>
      Sharpness.FluxEdgeCopy.Copy G (Function.update m e0 (m e0 + 1)))}
    (hp :
      p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A
        (Function.update m e0 (m e0 + 1)) e0)
    {owner : Sharpness.FluxEdgeCopy.Copy G
      (Function.update m e0 (m e0 + 1))}
    (howner : owner ∈ p.1) :
    p.1 ∈
      edgeCopySourceSectorContainingBothCopies G A
        (Function.update m e0 (m e0 + 1)) owner
        (edgeCopyIncrementInserted G m e0) := by
  classical
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  have hpbranch :=
    (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_mem G A M e0 p).mp hp
  have hK : p.1 ∈ edgeCopySourceSector G A M :=
    (edgeCopySourceSectorSelectedEdgeCopyPairs_mem
      (G := G) (A := A) (m := M) (e0 := e0) (p := p)).mp
      hpbranch.1 |>.1
  have hinserted : edgeCopyIncrementInserted G m e0 ∈ p.1 :=
    edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_incrementInserted_mem_of_update_zero
      G A m e0 hmzero hp
  exact
    (mem_edgeCopySourceSectorContainingBothCopies
      (G := G) (A := A) (m := M) (first := owner)
      (second := edgeCopyIncrementInserted G m e0) (K := p.1)).mpr
      ⟨hK, howner, hinserted⟩

set_option linter.style.longLine false in


theorem edgeCopySourceSectorContaining_incrementInserted_card_le_selectedEdgeCopyPairsInCurrent_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset) :
    (edgeCopySourceSectorContainingCopy G A
        (Function.update m e0 (m e0 + 1))
        (edgeCopyIncrementInserted G m e0)).card ≤
      (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A
        (Function.update m e0 (m e0 + 1)) e0).card := by
  classical
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  let inserted : Sharpness.FluxEdgeCopy.Copy G M :=
    edgeCopyIncrementInserted G m e0
  refine
    Finset.card_le_card_of_injOn
      (fun K : Finset (Sharpness.FluxEdgeCopy.Copy G M) =>
        (⟨K, inserted⟩ :
          Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G M) =>
            Sharpness.FluxEdgeCopy.Copy G M))) ?_ ?_
  · intro K hK
    rcases
        (mem_edgeCopySourceSectorContainingCopy
          (G := G) (A := A) (m := M) (i := inserted) (K := K)).mp hK with
      ⟨hKsource, hinserted⟩
    exact
      (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_mem
        G A M e0
        (⟨K, inserted⟩ :
          Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G M) =>
            Sharpness.FluxEdgeCopy.Copy G M))).mpr
        ⟨(edgeCopySourceSectorSelectedEdgeCopyPairs_mem
            (G := G) (A := A) (m := M) (e0 := e0)
            (p :=
              (⟨K, inserted⟩ :
                Sigma
                  (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G M) =>
                    Sharpness.FluxEdgeCopy.Copy G M)))).mpr
            ⟨hKsource, by simp [inserted, edgeCopyIncrementInserted]⟩,
          hinserted⟩
  · intro K _hK L _hL hmap
    exact congrArg Sigma.fst hmap

set_option linter.style.longLine false in


theorem edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_card_le_containing_incrementInserted_card_of_update_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (hmzero : m e0 = 0) :
    (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A
        (Function.update m e0 (m e0 + 1)) e0).card ≤
      (edgeCopySourceSectorContainingCopy G A
        (Function.update m e0 (m e0 + 1))
        (edgeCopyIncrementInserted G m e0)).card := by
  classical
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  refine
    Finset.card_le_card_of_injOn
      (fun p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G M) =>
          Sharpness.FluxEdgeCopy.Copy G M) => p.1) ?_ ?_
  · intro p hp
    exact
      edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_fst_mem_containing_incrementInserted_of_update_zero
        G A m e0 hmzero hp
  · intro p hp q hq hpq
    rcases p with ⟨K, i⟩
    rcases q with ⟨L, j⟩
    dsimp at hpq ⊢
    subst L
    have hi :
        i = edgeCopyIncrementInserted G m e0 :=
      edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_selectedCopy_eq_incrementInserted_of_update_zero
        G A m e0 hmzero hp
    have hj :
        j = edgeCopyIncrementInserted G m e0 :=
      edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_selectedCopy_eq_incrementInserted_of_update_zero
        G A m e0 hmzero hq
    simp [hi, hj]

set_option linter.style.longLine false in


theorem edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_card_eq_containing_incrementInserted_card_of_update_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (hmzero : m e0 = 0) :
    (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A
        (Function.update m e0 (m e0 + 1)) e0).card =
      (edgeCopySourceSectorContainingCopy G A
        (Function.update m e0 (m e0 + 1))
        (edgeCopyIncrementInserted G m e0)).card := by
  exact
    le_antisymm
      (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_card_le_containing_incrementInserted_card_of_update_zero
        G A m e0 hmzero)
      (edgeCopySourceSectorContaining_incrementInserted_card_le_selectedEdgeCopyPairsInCurrent_card
        G A m e0)

set_option linter.style.longLine false in


theorem edgeCopySourceSectorContaining_incrementInserted_card_pos_iff_selectedEdgeCopyPairsInCurrent_card_pos_of_update_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (hmzero : m e0 = 0) :
    0 <
        (edgeCopySourceSectorContainingCopy G A
          (Function.update m e0 (m e0 + 1))
          (edgeCopyIncrementInserted G m e0)).card ↔
      0 <
        (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A
          (Function.update m e0 (m e0 + 1)) e0).card := by
  rw [
    edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_card_eq_containing_incrementInserted_card_of_update_zero
      G A m e0 hmzero]

set_option linter.style.longLine false in


theorem edgeCopySourceSectorContaining_incrementInserted_nonempty_iff_selectedEdgeCopyPairsInCurrent_nonempty_of_update_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (hmzero : m e0 = 0) :
    (edgeCopySourceSectorContainingCopy G A
        (Function.update m e0 (m e0 + 1))
        (edgeCopyIncrementInserted G m e0)).Nonempty ↔
      (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A
        (Function.update m e0 (m e0 + 1)) e0).Nonempty := by
  constructor
  · intro hcont
    have hcont_card :
        0 <
          (edgeCopySourceSectorContainingCopy G A
            (Function.update m e0 (m e0 + 1))
            (edgeCopyIncrementInserted G m e0)).card :=
      Finset.Nonempty.card_pos hcont
    have hin_card :
        0 <
          (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A
            (Function.update m e0 (m e0 + 1)) e0).card :=
      (edgeCopySourceSectorContaining_incrementInserted_card_pos_iff_selectedEdgeCopyPairsInCurrent_card_pos_of_update_zero
        G A m e0 hmzero).mp hcont_card
    exact Finset.card_pos.mp hin_card
  · intro hin
    have hin_card :
        0 <
          (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A
            (Function.update m e0 (m e0 + 1)) e0).card :=
      Finset.Nonempty.card_pos hin
    have hcont_card :
        0 <
          (edgeCopySourceSectorContainingCopy G A
            (Function.update m e0 (m e0 + 1))
            (edgeCopyIncrementInserted G m e0)).card :=
      (edgeCopySourceSectorContaining_incrementInserted_card_pos_iff_selectedEdgeCopyPairsInCurrent_card_pos_of_update_zero
        G A m e0 hmzero).mpr hin_card
    exact Finset.card_pos.mp hcont_card

set_option linter.style.longLine false in


theorem edgeCopySourceSectorContaining_incrementInserted_card_not_pos_iff_selectedEdgeCopyPairsInCurrent_card_eq_zero_of_update_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (hmzero : m e0 = 0) :
    (¬ 0 <
        (edgeCopySourceSectorContainingCopy G A
          (Function.update m e0 (m e0 + 1))
          (edgeCopyIncrementInserted G m e0)).card) ↔
      (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A
        (Function.update m e0 (m e0 + 1)) e0).card = 0 := by
  rw [
    edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_card_eq_containing_incrementInserted_card_of_update_zero
      G A m e0 hmzero]
  constructor
  · intro hnot
    omega
  · intro hzero hpos
    omega

set_option linter.style.longLine false in


theorem edgeCopySourceSectorExcluding_incrementInserted_card_le_selectedEdgeCopyPairsOutsideCurrent_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset) :
    (edgeCopySourceSectorExcludingCopy G A
        (Function.update m e0 (m e0 + 1))
        (edgeCopyIncrementInserted G m e0)).card ≤
      (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A
        (Function.update m e0 (m e0 + 1)) e0).card := by
  classical
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  let inserted : Sharpness.FluxEdgeCopy.Copy G M :=
    edgeCopyIncrementInserted G m e0
  refine
    Finset.card_le_card_of_injOn
      (fun K : Finset (Sharpness.FluxEdgeCopy.Copy G M) =>
        (⟨K, inserted⟩ :
          Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G M) =>
            Sharpness.FluxEdgeCopy.Copy G M))) ?_ ?_
  · intro K hK
    rcases
        (mem_edgeCopySourceSectorExcludingCopy
          (G := G) (A := A) (m := M) (i := inserted) (K := K)).mp hK with
      ⟨hKsource, hinserted_not_mem⟩
    exact
      (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_mem
        G A M e0
        (⟨K, inserted⟩ :
          Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G M) =>
            Sharpness.FluxEdgeCopy.Copy G M))).mpr
        ⟨(edgeCopySourceSectorSelectedEdgeCopyPairs_mem
            (G := G) (A := A) (m := M) (e0 := e0)
            (p :=
              (⟨K, inserted⟩ :
                Sigma
                  (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G M) =>
                    Sharpness.FluxEdgeCopy.Copy G M)))).mpr
            ⟨hKsource, by simp [inserted, edgeCopyIncrementInserted]⟩,
          hinserted_not_mem⟩
  · intro K _hK L _hL hmap
    exact congrArg Sigma.fst hmap

set_option linter.style.longLine false in


theorem edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_card_le_excluding_incrementInserted_card_of_update_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (hmzero : m e0 = 0) :
    (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A
        (Function.update m e0 (m e0 + 1)) e0).card ≤
      (edgeCopySourceSectorExcludingCopy G A
        (Function.update m e0 (m e0 + 1))
        (edgeCopyIncrementInserted G m e0)).card := by
  classical
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  refine
    Finset.card_le_card_of_injOn
      (fun p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G M) =>
          Sharpness.FluxEdgeCopy.Copy G M) => p.1) ?_ ?_
  · intro p hp
    exact
      edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_fst_mem_excluding_incrementInserted_of_update_zero
        G A m e0 hmzero hp
  · intro p hp q hq hpq
    rcases p with ⟨K, i⟩
    rcases q with ⟨L, j⟩
    dsimp at hpq ⊢
    subst L
    have hi :
        i = edgeCopyIncrementInserted G m e0 :=
      edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_selectedCopy_eq_incrementInserted_of_update_zero
        G A m e0 hmzero hp
    have hj :
        j = edgeCopyIncrementInserted G m e0 :=
      edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_selectedCopy_eq_incrementInserted_of_update_zero
        G A m e0 hmzero hq
    simp [hi, hj]

set_option linter.style.longLine false in


theorem edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_card_eq_excluding_incrementInserted_card_of_update_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (hmzero : m e0 = 0) :
    (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A
        (Function.update m e0 (m e0 + 1)) e0).card =
      (edgeCopySourceSectorExcludingCopy G A
        (Function.update m e0 (m e0 + 1))
        (edgeCopyIncrementInserted G m e0)).card := by
  exact
    le_antisymm
      (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_card_le_excluding_incrementInserted_card_of_update_zero
        G A m e0 hmzero)
      (edgeCopySourceSectorExcluding_incrementInserted_card_le_selectedEdgeCopyPairsOutsideCurrent_card
        G A m e0)

set_option linter.style.longLine false in


theorem edgeCopySourceSectorExcluding_incrementInserted_card_pos_iff_selectedEdgeCopyPairsOutsideCurrent_card_pos_of_update_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (hmzero : m e0 = 0) :
    0 <
        (edgeCopySourceSectorExcludingCopy G A
          (Function.update m e0 (m e0 + 1))
          (edgeCopyIncrementInserted G m e0)).card ↔
      0 <
        (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A
          (Function.update m e0 (m e0 + 1)) e0).card := by
  rw [
    edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_card_eq_excluding_incrementInserted_card_of_update_zero
      G A m e0 hmzero]

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpoint_containing_incrementInserted_card_pos_iff_selectedEdgeCopyPairsInCurrent_card_pos_of_update_zero
    {n : ℕ} {v : FK.boxVerts 3 n}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hmzero : m e0 = 0) :
    0 <
        (edgeCopySourceSectorContainingCopy
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1))
          (edgeCopyIncrementInserted (FK.boxGraph 3 (2 * n)) m e0)).card ↔
      0 <
        (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1)) e0).card := by
  exact
    edgeCopySourceSectorContaining_incrementInserted_card_pos_iff_selectedEdgeCopyPairsInCurrent_card_pos_of_update_zero
      (FK.boxGraph 3 (2 * n)) (doubledBoxOriginToInnerEndpointSource n v)
      m e0 hmzero

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpoint_containing_incrementInserted_nonempty_iff_selectedEdgeCopyPairsInCurrent_nonempty_of_update_zero
    {n : ℕ} {v : FK.boxVerts 3 n}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hmzero : m e0 = 0) :
    (edgeCopySourceSectorContainingCopy
      (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n v)
      (Function.update m e0 (m e0 + 1))
      (edgeCopyIncrementInserted (FK.boxGraph 3 (2 * n)) m e0)).Nonempty ↔
    (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
      (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n v)
      (Function.update m e0 (m e0 + 1)) e0).Nonempty := by
  exact
    edgeCopySourceSectorContaining_incrementInserted_nonempty_iff_selectedEdgeCopyPairsInCurrent_nonempty_of_update_zero
      (FK.boxGraph 3 (2 * n)) (doubledBoxOriginToInnerEndpointSource n v)
      m e0 hmzero

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpoint_containing_incrementInserted_card_not_pos_iff_selectedEdgeCopyPairsInCurrent_card_eq_zero_of_update_zero
    {n : ℕ} {v : FK.boxVerts 3 n}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hmzero : m e0 = 0) :
    (¬ 0 <
        (edgeCopySourceSectorContainingCopy
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1))
          (edgeCopyIncrementInserted (FK.boxGraph 3 (2 * n)) m e0)).card) ↔
      (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1)) e0).card = 0 := by
  exact
    edgeCopySourceSectorContaining_incrementInserted_card_not_pos_iff_selectedEdgeCopyPairsInCurrent_card_eq_zero_of_update_zero
      (FK.boxGraph 3 (2 * n)) (doubledBoxOriginToInnerEndpointSource n v)
      m e0 hmzero

set_option linter.style.longLine false in


theorem edgeCopySourceSectorContaining_incrementInserted_card_pos_iff_outsideCurrent_card_lt_selectedEdgeCopyPairs_card_of_update_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (hmzero : m e0 = 0) :
    0 <
        (edgeCopySourceSectorContainingCopy G A
          (Function.update m e0 (m e0 + 1))
          (edgeCopyIncrementInserted G m e0)).card ↔
      (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A
          (Function.update m e0 (m e0 + 1)) e0).card <
        (edgeCopySourceSectorSelectedEdgeCopyPairs G A
          (Function.update m e0 (m e0 + 1)) e0).card := by
  classical
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  let containing :=
    edgeCopySourceSectorContainingCopy G A M (edgeCopyIncrementInserted G m e0)
  let inBranch := edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A M e0
  let outsideBranch :=
    edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A M e0
  let totalBranch := edgeCopySourceSectorSelectedEdgeCopyPairs G A M e0
  have hiff : 0 < containing.card ↔ 0 < inBranch.card := by
    simpa [containing, inBranch, M] using
      edgeCopySourceSectorContaining_incrementInserted_card_pos_iff_selectedEdgeCopyPairsInCurrent_card_pos_of_update_zero
        G A m e0 hmzero
  have hsplit : inBranch.card + outsideBranch.card = totalBranch.card := by
    simpa [inBranch, outsideBranch, totalBranch, M] using
      edgeCopySourceSectorSelectedEdgeCopyPairs_branch_card_add_eq_total_card
        G A M e0
  change 0 < containing.card ↔ outsideBranch.card < totalBranch.card
  constructor
  · intro hcont
    have hin : 0 < inBranch.card := hiff.mp hcont
    omega
  · intro hlt
    exact hiff.mpr (by omega)

set_option linter.style.longLine false in


theorem edgeCopySourceSectorContaining_incrementInserted_card_not_pos_iff_outsideCurrent_exhausts_selectedEdgeCopyPairs_of_update_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (hmzero : m e0 = 0) :
    (¬ 0 <
        (edgeCopySourceSectorContainingCopy G A
          (Function.update m e0 (m e0 + 1))
          (edgeCopyIncrementInserted G m e0)).card) ↔
      (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A
          (Function.update m e0 (m e0 + 1)) e0).card =
        (edgeCopySourceSectorSelectedEdgeCopyPairs G A
          (Function.update m e0 (m e0 + 1)) e0).card := by
  classical
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  let containing :=
    edgeCopySourceSectorContainingCopy G A M (edgeCopyIncrementInserted G m e0)
  let inBranch := edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A M e0
  let outsideBranch :=
    edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A M e0
  let totalBranch := edgeCopySourceSectorSelectedEdgeCopyPairs G A M e0
  have hiff :
      0 < containing.card ↔ outsideBranch.card < totalBranch.card := by
    simpa [containing, outsideBranch, totalBranch, M] using
      edgeCopySourceSectorContaining_incrementInserted_card_pos_iff_outsideCurrent_card_lt_selectedEdgeCopyPairs_card_of_update_zero
        G A m e0 hmzero
  have hsplit : inBranch.card + outsideBranch.card = totalBranch.card := by
    simpa [inBranch, outsideBranch, totalBranch, M] using
      edgeCopySourceSectorSelectedEdgeCopyPairs_branch_card_add_eq_total_card
        G A M e0
  change (¬ 0 < containing.card) ↔ outsideBranch.card = totalBranch.card
  constructor
  · intro hnot
    have hnotlt : ¬ outsideBranch.card < totalBranch.card := by
      intro hlt
      exact hnot (hiff.mpr hlt)
    omega
  · intro hexhaust hcont
    have hlt : outsideBranch.card < totalBranch.card := hiff.mp hcont
    omega

set_option linter.style.longLine false in


theorem edgeCopySourceSectorContaining_incrementInserted_card_pos_or_outsideCurrent_exhausts_selectedEdgeCopyPairs_of_update_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (hmzero : m e0 = 0) :
    0 <
        (edgeCopySourceSectorContainingCopy G A
          (Function.update m e0 (m e0 + 1))
          (edgeCopyIncrementInserted G m e0)).card ∨
      (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A
          (Function.update m e0 (m e0 + 1)) e0).card =
        (edgeCopySourceSectorSelectedEdgeCopyPairs G A
          (Function.update m e0 (m e0 + 1)) e0).card := by
  classical
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  let containing :=
    edgeCopySourceSectorContainingCopy G A M (edgeCopyIncrementInserted G m e0)
  let inBranch := edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A M e0
  let outsideBranch :=
    edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A M e0
  let totalBranch := edgeCopySourceSectorSelectedEdgeCopyPairs G A M e0
  change 0 < containing.card ∨ outsideBranch.card = totalBranch.card
  by_cases hcont : 0 < containing.card
  · exact Or.inl hcont
  · right
    have hiff :
        0 < containing.card ↔ outsideBranch.card < totalBranch.card := by
      simpa [containing, outsideBranch, totalBranch, M] using
        edgeCopySourceSectorContaining_incrementInserted_card_pos_iff_outsideCurrent_card_lt_selectedEdgeCopyPairs_card_of_update_zero
          G A m e0 hmzero
    have hsplit : inBranch.card + outsideBranch.card = totalBranch.card := by
      simpa [inBranch, outsideBranch, totalBranch, M] using
        edgeCopySourceSectorSelectedEdgeCopyPairs_branch_card_add_eq_total_card
          G A M e0
    have hnotlt : ¬ outsideBranch.card < totalBranch.card := by
      intro hlt
      exact hcont (hiff.mpr hlt)
    omega

set_option linter.style.longLine false in


theorem edgeCopySourceSectorContaining_incrementInserted_nonempty_or_outsideCurrent_exhausts_selectedEdgeCopyPairs_of_update_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (hmzero : m e0 = 0) :
    (edgeCopySourceSectorContainingCopy G A
        (Function.update m e0 (m e0 + 1))
        (edgeCopyIncrementInserted G m e0)).Nonempty ∨
      (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A
          (Function.update m e0 (m e0 + 1)) e0).card =
        (edgeCopySourceSectorSelectedEdgeCopyPairs G A
          (Function.update m e0 (m e0 + 1)) e0).card := by
  rcases
      edgeCopySourceSectorContaining_incrementInserted_card_pos_or_outsideCurrent_exhausts_selectedEdgeCopyPairs_of_update_zero
        G A m e0 hmzero with hpos | hexhaust
  · exact Or.inl (Finset.card_pos.mp hpos)
  · exact Or.inr hexhaust

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpoint_containing_incrementInserted_card_pos_iff_outsideCurrent_card_lt_selectedEdgeCopyPairs_card_of_update_zero
    {n : ℕ} {v : FK.boxVerts 3 n}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hmzero : m e0 = 0) :
    0 <
        (edgeCopySourceSectorContainingCopy
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1))
          (edgeCopyIncrementInserted (FK.boxGraph 3 (2 * n)) m e0)).card ↔
      (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1)) e0).card <
        (edgeCopySourceSectorSelectedEdgeCopyPairs
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1)) e0).card := by
  exact
    edgeCopySourceSectorContaining_incrementInserted_card_pos_iff_outsideCurrent_card_lt_selectedEdgeCopyPairs_card_of_update_zero
      (FK.boxGraph 3 (2 * n)) (doubledBoxOriginToInnerEndpointSource n v)
      m e0 hmzero

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpoint_containing_incrementInserted_card_not_pos_iff_outsideCurrent_exhausts_selectedEdgeCopyPairs_of_update_zero
    {n : ℕ} {v : FK.boxVerts 3 n}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hmzero : m e0 = 0) :
    (¬ 0 <
        (edgeCopySourceSectorContainingCopy
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1))
          (edgeCopyIncrementInserted (FK.boxGraph 3 (2 * n)) m e0)).card) ↔
      (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1)) e0).card =
        (edgeCopySourceSectorSelectedEdgeCopyPairs
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1)) e0).card := by
  exact
    edgeCopySourceSectorContaining_incrementInserted_card_not_pos_iff_outsideCurrent_exhausts_selectedEdgeCopyPairs_of_update_zero
      (FK.boxGraph 3 (2 * n)) (doubledBoxOriginToInnerEndpointSource n v)
      m e0 hmzero

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpoint_containing_incrementInserted_card_pos_or_outsideCurrent_exhausts_selectedEdgeCopyPairs_of_update_zero
    {n : ℕ} {v : FK.boxVerts 3 n}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hmzero : m e0 = 0) :
    0 <
        (edgeCopySourceSectorContainingCopy
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1))
          (edgeCopyIncrementInserted (FK.boxGraph 3 (2 * n)) m e0)).card ∨
      (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1)) e0).card =
        (edgeCopySourceSectorSelectedEdgeCopyPairs
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1)) e0).card := by
  exact
    edgeCopySourceSectorContaining_incrementInserted_card_pos_or_outsideCurrent_exhausts_selectedEdgeCopyPairs_of_update_zero
      (FK.boxGraph 3 (2 * n)) (doubledBoxOriginToInnerEndpointSource n v)
      m e0 hmzero

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpoint_containing_incrementInserted_nonempty_or_outsideCurrent_exhausts_selectedEdgeCopyPairs_of_update_zero
    {n : ℕ} {v : FK.boxVerts 3 n}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hmzero : m e0 = 0) :
    (edgeCopySourceSectorContainingCopy
      (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n v)
      (Function.update m e0 (m e0 + 1))
      (edgeCopyIncrementInserted (FK.boxGraph 3 (2 * n)) m e0)).Nonempty ∨
    (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (Function.update m e0 (m e0 + 1)) e0).card =
      (edgeCopySourceSectorSelectedEdgeCopyPairs
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (Function.update m e0 (m e0 + 1)) e0).card := by
  exact
    edgeCopySourceSectorContaining_incrementInserted_nonempty_or_outsideCurrent_exhausts_selectedEdgeCopyPairs_of_update_zero
      (FK.boxGraph 3 (2 * n)) (doubledBoxOriginToInnerEndpointSource n v)
      m e0 hmzero

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpoint_outsideCurrent_card_eq_switchedSourceSector_card_of_update_zero_exhausts
    {n : ℕ} {v : FK.boxVerts 3 n}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hmzero : m e0 = 0)
    (hexhaust :
      (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1)) e0).card =
        (edgeCopySourceSectorSelectedEdgeCopyPairs
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1)) e0).card) :
    (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (Function.update m e0 (m e0 + 1)) e0).card =
      (edgeCopySourceSector
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (Function.update m e0 (m e0 + 1))).card := by
  calc
    (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (Function.update m e0 (m e0 + 1)) e0).card =
        (edgeCopySourceSectorSelectedEdgeCopyPairs
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1)) e0).card := hexhaust
    _ =
        (edgeCopySourceSector
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1))).card *
          (Function.update m e0 (m e0 + 1)) e0 := by
          rw [edgeCopySourceSectorSelectedEdgeCopyPairs_card]
    _ =
        (edgeCopySourceSector
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1))).card := by
          simp [hmzero]

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpoint_predecessorSourceSector_nonempty_or_residualContaining_or_outsideCurrent_exhausts_update_zero
    {n : ℕ} {v w : FK.boxVerts 3 n}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hmzero : m e0 = 0) :
    (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m).Nonempty ∨
      ((¬ (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w) m).Nonempty) ∧
        (edgeCopySourceSectorContainingCopy
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1))
          (edgeCopyIncrementInserted (FK.boxGraph 3 (2 * n)) m e0)).Nonempty) ∨
      ((¬ (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w) m).Nonempty) ∧
        (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n v)
            (Function.update m e0 (m e0 + 1)) e0).card =
          (edgeCopySourceSectorSelectedEdgeCopyPairs
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n v)
            (Function.update m e0 (m e0 + 1)) e0).card) := by
  by_cases hsource :
      (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m).Nonempty
  · exact Or.inl hsource
  · right
    rcases
        doubledBoxOriginToInnerEndpoint_containing_incrementInserted_nonempty_or_outsideCurrent_exhausts_selectedEdgeCopyPairs_of_update_zero
          (n := n) (v := v) (e0 := e0) (m := m) hmzero with hcont | hexhaust
    · exact Or.inl ⟨hsource, hcont⟩
    · exact Or.inr ⟨hsource, hexhaust⟩

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpoint_residualContaining_nonempty_iff_predecessorSourceSector_not_nonempty_and_outsideCurrent_card_lt_selectedEdgeCopyPairs_card_update_zero
    {n : ℕ} {v w : FK.boxVerts 3 n}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hmzero : m e0 = 0) :
    ((¬ (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w) m).Nonempty) ∧
        (edgeCopySourceSectorContainingCopy
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1))
          (edgeCopyIncrementInserted (FK.boxGraph 3 (2 * n)) m e0)).Nonempty) ↔
      ((¬ (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w) m).Nonempty) ∧
        (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n v)
            (Function.update m e0 (m e0 + 1)) e0).card <
          (edgeCopySourceSectorSelectedEdgeCopyPairs
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n v)
            (Function.update m e0 (m e0 + 1)) e0).card) := by
  constructor
  · intro hres
    constructor
    · exact hres.1
    · have hcont_card :
          0 <
            (edgeCopySourceSectorContainingCopy
              (FK.boxGraph 3 (2 * n))
              (doubledBoxOriginToInnerEndpointSource n v)
              (Function.update m e0 (m e0 + 1))
              (edgeCopyIncrementInserted (FK.boxGraph 3 (2 * n)) m e0)).card :=
        Finset.Nonempty.card_pos hres.2
      exact
        (doubledBoxOriginToInnerEndpoint_containing_incrementInserted_card_pos_iff_outsideCurrent_card_lt_selectedEdgeCopyPairs_card_of_update_zero
          (n := n) (v := v) (e0 := e0) (m := m) hmzero).mp hcont_card
  · intro hres
    constructor
    · exact hres.1
    · have hcont_card :
          0 <
            (edgeCopySourceSectorContainingCopy
              (FK.boxGraph 3 (2 * n))
              (doubledBoxOriginToInnerEndpointSource n v)
              (Function.update m e0 (m e0 + 1))
              (edgeCopyIncrementInserted (FK.boxGraph 3 (2 * n)) m e0)).card :=
        (doubledBoxOriginToInnerEndpoint_containing_incrementInserted_card_pos_iff_outsideCurrent_card_lt_selectedEdgeCopyPairs_card_of_update_zero
          (n := n) (v := v) (e0 := e0) (m := m) hmzero).mpr hres.2
      exact Finset.card_pos.mp hcont_card

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpoint_predecessorSourceSector_nonempty_or_residualNonexhaustion_or_outsideCurrent_exhausts_update_zero
    {n : ℕ} {v w : FK.boxVerts 3 n}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hmzero : m e0 = 0) :
    (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m).Nonempty ∨
      ((¬ (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w) m).Nonempty) ∧
        (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n v)
            (Function.update m e0 (m e0 + 1)) e0).card <
          (edgeCopySourceSectorSelectedEdgeCopyPairs
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n v)
            (Function.update m e0 (m e0 + 1)) e0).card) ∨
      ((¬ (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w) m).Nonempty) ∧
        (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n v)
            (Function.update m e0 (m e0 + 1)) e0).card =
          (edgeCopySourceSectorSelectedEdgeCopyPairs
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n v)
            (Function.update m e0 (m e0 + 1)) e0).card) := by
  rcases
      doubledBoxOriginToInnerEndpoint_predecessorSourceSector_nonempty_or_residualContaining_or_outsideCurrent_exhausts_update_zero
        (n := n) (v := v) (w := w) (e0 := e0) (m := m) hmzero with
    hsource | hrest
  · exact Or.inl hsource
  · right
    rcases hrest with hres | hexhaust
    · exact Or.inl
        ((doubledBoxOriginToInnerEndpoint_residualContaining_nonempty_iff_predecessorSourceSector_not_nonempty_and_outsideCurrent_card_lt_selectedEdgeCopyPairs_card_update_zero
          (n := n) (v := v) (w := w) (e0 := e0) (m := m) hmzero).mp hres)
    · exact Or.inr hexhaust

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpoint_residualContaining_nonempty_iff_predecessorSourceSector_not_nonempty_and_selectedEdgeCopyPairsInCurrent_nonempty_update_zero
    {n : ℕ} {v w : FK.boxVerts 3 n}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hmzero : m e0 = 0) :
    ((¬ (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w) m).Nonempty) ∧
        (edgeCopySourceSectorContainingCopy
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1))
          (edgeCopyIncrementInserted (FK.boxGraph 3 (2 * n)) m e0)).Nonempty) ↔
      ((¬ (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w) m).Nonempty) ∧
        (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1)) e0).Nonempty) := by
  constructor
  · intro hres
    exact
      ⟨hres.1,
        (doubledBoxOriginToInnerEndpoint_containing_incrementInserted_nonempty_iff_selectedEdgeCopyPairsInCurrent_nonempty_of_update_zero
          (n := n) (v := v) (e0 := e0) (m := m) hmzero).mp hres.2⟩
  · intro hres
    exact
      ⟨hres.1,
        (doubledBoxOriginToInnerEndpoint_containing_incrementInserted_nonempty_iff_selectedEdgeCopyPairsInCurrent_nonempty_of_update_zero
          (n := n) (v := v) (e0 := e0) (m := m) hmzero).mpr hres.2⟩

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpoint_predecessorSourceSector_nonempty_or_residualInCurrent_or_outsideCurrent_exhausts_update_zero
    {n : ℕ} {v w : FK.boxVerts 3 n}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hmzero : m e0 = 0) :
    (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m).Nonempty ∨
      ((¬ (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w) m).Nonempty) ∧
        (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1)) e0).Nonempty) ∨
      ((¬ (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w) m).Nonempty) ∧
        (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n v)
            (Function.update m e0 (m e0 + 1)) e0).card =
          (edgeCopySourceSectorSelectedEdgeCopyPairs
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n v)
            (Function.update m e0 (m e0 + 1)) e0).card) := by
  rcases
      doubledBoxOriginToInnerEndpoint_predecessorSourceSector_nonempty_or_residualContaining_or_outsideCurrent_exhausts_update_zero
        (n := n) (v := v) (w := w) (e0 := e0) (m := m) hmzero with
    hsource | hrest
  · exact Or.inl hsource
  · right
    rcases hrest with hres | hexhaust
    · exact Or.inl
        ((doubledBoxOriginToInnerEndpoint_residualContaining_nonempty_iff_predecessorSourceSector_not_nonempty_and_selectedEdgeCopyPairsInCurrent_nonempty_update_zero
          (n := n) (v := v) (w := w) (e0 := e0) (m := m) hmzero).mp hres)
    · exact Or.inr hexhaust

set_option linter.style.longLine false in


theorem edgeCopySourceSectorContaining_incrementInserted_owner_branch_card_add_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (owner : Sharpness.FluxEdgeCopy.Copy G
      (Function.update m e0 (m e0 + 1))) :
    (edgeCopySourceSectorContainingBothCopies G A
        (Function.update m e0 (m e0 + 1)) owner
        (edgeCopyIncrementInserted G m e0)).card +
      (edgeCopySourceSectorContainingAndExcludingCopy G A
        (Function.update m e0 (m e0 + 1))
        (edgeCopyIncrementInserted G m e0) owner).card =
      (edgeCopySourceSectorContainingCopy G A
        (Function.update m e0 (m e0 + 1))
        (edgeCopyIncrementInserted G m e0)).card := by
  classical
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  let inserted : Sharpness.FluxEdgeCopy.Copy G M :=
    edgeCopyIncrementInserted G m e0
  have hsplit :=
    edgeCopySourceSectorContainingCopy_branch_card_add_eq G A M inserted owner
  rw [edgeCopySourceSectorContainingBothCopies_card_comm G A M owner inserted]
  simpa [M, inserted] using hsplit

set_option linter.style.longLine false in


theorem edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_card_eq_owner_incrementInserted_add_incrementInserted_excluding_owner_of_update_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (hmzero : m e0 = 0)
    (owner : Sharpness.FluxEdgeCopy.Copy G
      (Function.update m e0 (m e0 + 1))) :
    (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A
        (Function.update m e0 (m e0 + 1)) e0).card =
      (edgeCopySourceSectorContainingBothCopies G A
        (Function.update m e0 (m e0 + 1)) owner
        (edgeCopyIncrementInserted G m e0)).card +
      (edgeCopySourceSectorContainingAndExcludingCopy G A
        (Function.update m e0 (m e0 + 1))
        (edgeCopyIncrementInserted G m e0) owner).card := by
  calc
    (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A
        (Function.update m e0 (m e0 + 1)) e0).card =
      (edgeCopySourceSectorContainingCopy G A
        (Function.update m e0 (m e0 + 1))
        (edgeCopyIncrementInserted G m e0)).card :=
        edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_card_eq_containing_incrementInserted_card_of_update_zero
          G A m e0 hmzero
    _ =
      (edgeCopySourceSectorContainingBothCopies G A
        (Function.update m e0 (m e0 + 1)) owner
        (edgeCopyIncrementInserted G m e0)).card +
      (edgeCopySourceSectorContainingAndExcludingCopy G A
        (Function.update m e0 (m e0 + 1))
        (edgeCopyIncrementInserted G m e0) owner).card := by
        exact
          (edgeCopySourceSectorContaining_incrementInserted_owner_branch_card_add_eq
            G A m e0 owner).symm

set_option linter.style.longLine false in


theorem edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_card_mul_eq_owner_incrementInserted_add_incrementInserted_excluding_owner_mul_of_update_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (hmzero : m e0 = 0)
    (owner : Sharpness.FluxEdgeCopy.Copy G
      (Function.update m e0 (m e0 + 1))) (base : ℝ) :
    ((edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A
        (Function.update m e0 (m e0 + 1)) e0).card : ℝ) * base =
      ((edgeCopySourceSectorContainingBothCopies G A
        (Function.update m e0 (m e0 + 1)) owner
        (edgeCopyIncrementInserted G m e0)).card : ℝ) * base +
      ((edgeCopySourceSectorContainingAndExcludingCopy G A
        (Function.update m e0 (m e0 + 1))
        (edgeCopyIncrementInserted G m e0) owner).card : ℝ) * base := by
  have hcard :=
    edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_card_eq_owner_incrementInserted_add_incrementInserted_excluding_owner_of_update_zero
      G A m e0 hmzero owner
  have hcast :
      ((edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A
          (Function.update m e0 (m e0 + 1)) e0).card : ℝ) =
        ((edgeCopySourceSectorContainingBothCopies G A
          (Function.update m e0 (m e0 + 1)) owner
          (edgeCopyIncrementInserted G m e0)).card : ℝ) +
        ((edgeCopySourceSectorContainingAndExcludingCopy G A
          (Function.update m e0 (m e0 + 1))
          (edgeCopyIncrementInserted G m e0) owner).card : ℝ) := by
    exact_mod_cast hcard
  rw [hcast]
  ring

set_option linter.style.longLine false in

theorem beta_mul_edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_card_mul_eq_owner_incrementInserted_add_incrementInserted_excluding_owner_mul_of_update_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (hmzero : m e0 = 0)
    (owner : Sharpness.FluxEdgeCopy.Copy G
      (Function.update m e0 (m e0 + 1))) (β base : ℝ) :
    β *
        (((edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A
          (Function.update m e0 (m e0 + 1)) e0).card : ℝ) * base) =
      β *
          (((edgeCopySourceSectorContainingBothCopies G A
            (Function.update m e0 (m e0 + 1)) owner
            (edgeCopyIncrementInserted G m e0)).card : ℝ) * base) +
        β *
          (((edgeCopySourceSectorContainingAndExcludingCopy G A
            (Function.update m e0 (m e0 + 1))
            (edgeCopyIncrementInserted G m e0) owner).card : ℝ) * base) := by
  rw [
    edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_card_mul_eq_owner_incrementInserted_add_incrementInserted_excluding_owner_mul_of_update_zero
      G A m e0 hmzero owner base]
  ring

set_option linter.style.longLine false in


theorem edgeCopySourceSectorContaining_incrementInserted_excluding_owner_mem_selectedEdgeCopyPairsOutsideCurrent_ownerEdge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (owner : Sharpness.FluxEdgeCopy.Copy G
      (Function.update m e0 (m e0 + 1)))
    {K : Finset (Sharpness.FluxEdgeCopy.Copy G
      (Function.update m e0 (m e0 + 1)))}
    (hK :
      K ∈ edgeCopySourceSectorContainingAndExcludingCopy G A
        (Function.update m e0 (m e0 + 1))
        (edgeCopyIncrementInserted G m e0) owner) :
    (⟨K, owner⟩ :
        Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G
          (Function.update m e0 (m e0 + 1))) =>
          Sharpness.FluxEdgeCopy.Copy G
            (Function.update m e0 (m e0 + 1)))) ∈
      edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A
        (Function.update m e0 (m e0 + 1)) owner.1 := by
  classical
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  let inserted : Sharpness.FluxEdgeCopy.Copy G M :=
    edgeCopyIncrementInserted G m e0
  rcases
      (mem_edgeCopySourceSectorContainingAndExcludingCopy
        (G := G) (A := A) (m := M) (inside := inserted)
        (outside := owner) (K := K)).mp (by simpa [M, inserted] using hK) with
    ⟨hKsource, _hinserted, howner_not_mem⟩
  exact
    (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_mem
      G A M owner.1
      (⟨K, owner⟩ :
        Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G M) =>
          Sharpness.FluxEdgeCopy.Copy G M))).mpr
      ⟨(edgeCopySourceSectorSelectedEdgeCopyPairs_mem
          (G := G) (A := A) (m := M) (e0 := owner.1)
          (p :=
            (⟨K, owner⟩ :
              Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G M) =>
                Sharpness.FluxEdgeCopy.Copy G M)))).mpr
          ⟨hKsource, rfl⟩,
        howner_not_mem⟩

set_option linter.style.longLine false in


theorem edgeCopySourceSectorContaining_incrementInserted_excluding_owner_mem_selectedEdgeCopyPairsOutsideCurrent_of_ownerEdge_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 ew : ↥G.edgeFinset)
    (owner : Sharpness.FluxEdgeCopy.Copy G
      (Function.update m e0 (m e0 + 1)))
    (hownerEdge : owner.1 = ew)
    {K : Finset (Sharpness.FluxEdgeCopy.Copy G
      (Function.update m e0 (m e0 + 1)))}
    (hK :
      K ∈ edgeCopySourceSectorContainingAndExcludingCopy G A
        (Function.update m e0 (m e0 + 1))
        (edgeCopyIncrementInserted G m e0) owner) :
    (⟨K, owner⟩ :
        Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G
          (Function.update m e0 (m e0 + 1))) =>
          Sharpness.FluxEdgeCopy.Copy G
            (Function.update m e0 (m e0 + 1)))) ∈
      edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A
        (Function.update m e0 (m e0 + 1)) ew := by
  rw [← hownerEdge]
  exact
    edgeCopySourceSectorContaining_incrementInserted_excluding_owner_mem_selectedEdgeCopyPairsOutsideCurrent_ownerEdge
      G A m e0 owner hK

set_option linter.style.longLine false in


theorem edgeCopySourceSectorContaining_incrementInserted_excluding_owner_card_le_selectedEdgeCopyPairsOutsideCurrent_ownerEdge_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (owner : Sharpness.FluxEdgeCopy.Copy G
      (Function.update m e0 (m e0 + 1))) :
    (edgeCopySourceSectorContainingAndExcludingCopy G A
        (Function.update m e0 (m e0 + 1))
        (edgeCopyIncrementInserted G m e0) owner).card ≤
      (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A
        (Function.update m e0 (m e0 + 1)) owner.1).card := by
  exact
    edgeCopySourceSectorContainingAndExcludingCopy_card_le_selectedEdgeCopyPairsOutsideCurrent_card
      G A (Function.update m e0 (m e0 + 1)) owner.1
      (edgeCopyIncrementInserted G m e0) owner rfl

set_option linter.style.longLine false in

theorem edgeCopySourceSectorContaining_incrementInserted_excluding_owner_card_le_selectedEdgeCopyPairsOutsideCurrent_card_of_ownerEdge_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 ew : ↥G.edgeFinset)
    (owner : Sharpness.FluxEdgeCopy.Copy G
      (Function.update m e0 (m e0 + 1)))
    (hownerEdge : owner.1 = ew) :
    (edgeCopySourceSectorContainingAndExcludingCopy G A
        (Function.update m e0 (m e0 + 1))
        (edgeCopyIncrementInserted G m e0) owner).card ≤
      (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A
        (Function.update m e0 (m e0 + 1)) ew).card := by
  rw [← hownerEdge]
  exact
    edgeCopySourceSectorContaining_incrementInserted_excluding_owner_card_le_selectedEdgeCopyPairsOutsideCurrent_ownerEdge_card
      G A m e0 owner

set_option linter.style.longLine false in


theorem edgeCopySourceSectorContaining_incrementInserted_excluding_owner_card_mul_le_selectedEdgeCopyPairsOutsideCurrent_ownerEdge_card_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (owner : Sharpness.FluxEdgeCopy.Copy G
      (Function.update m e0 (m e0 + 1))) (base : ℝ)
    (hbase : 0 ≤ base) :
    ((edgeCopySourceSectorContainingAndExcludingCopy G A
        (Function.update m e0 (m e0 + 1))
        (edgeCopyIncrementInserted G m e0) owner).card : ℝ) * base ≤
      ((edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A
        (Function.update m e0 (m e0 + 1)) owner.1).card : ℝ) * base := by
  have hcard_nat :=
    edgeCopySourceSectorContaining_incrementInserted_excluding_owner_card_le_selectedEdgeCopyPairsOutsideCurrent_ownerEdge_card
      G A m e0 owner
  have hcard_real :
      ((edgeCopySourceSectorContainingAndExcludingCopy G A
          (Function.update m e0 (m e0 + 1))
          (edgeCopyIncrementInserted G m e0) owner).card : ℝ) ≤
        ((edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A
          (Function.update m e0 (m e0 + 1)) owner.1).card : ℝ) := by
    exact_mod_cast hcard_nat
  exact mul_le_mul_of_nonneg_right hcard_real hbase

set_option linter.style.longLine false in


theorem edgeCopySourceSectorContaining_incrementInserted_excluding_owner_card_mul_le_selectedEdgeCopyPairsOutsideCurrent_card_mul_of_ownerEdge_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 ew : ↥G.edgeFinset)
    (owner : Sharpness.FluxEdgeCopy.Copy G
      (Function.update m e0 (m e0 + 1)))
    (hownerEdge : owner.1 = ew) (base : ℝ) (hbase : 0 ≤ base) :
    ((edgeCopySourceSectorContainingAndExcludingCopy G A
        (Function.update m e0 (m e0 + 1))
        (edgeCopyIncrementInserted G m e0) owner).card : ℝ) * base ≤
      ((edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A
        (Function.update m e0 (m e0 + 1)) ew).card : ℝ) * base := by
  rw [← hownerEdge]
  exact
    edgeCopySourceSectorContaining_incrementInserted_excluding_owner_card_mul_le_selectedEdgeCopyPairsOutsideCurrent_ownerEdge_card_mul
      G A m e0 owner base hbase

set_option linter.style.longLine false in


theorem beta_mul_edgeCopySourceSectorContaining_incrementInserted_excluding_owner_card_mul_le_selectedEdgeCopyPairsOutsideCurrent_ownerEdge_card_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (owner : Sharpness.FluxEdgeCopy.Copy G
      (Function.update m e0 (m e0 + 1))) (β base : ℝ)
    (hβ : 0 ≤ β) (hbase : 0 ≤ base) :
    β *
        (((edgeCopySourceSectorContainingAndExcludingCopy G A
          (Function.update m e0 (m e0 + 1))
          (edgeCopyIncrementInserted G m e0) owner).card : ℝ) * base) ≤
      β *
        (((edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A
          (Function.update m e0 (m e0 + 1)) owner.1).card : ℝ) * base) := by
  exact
    mul_le_mul_of_nonneg_left
      (edgeCopySourceSectorContaining_incrementInserted_excluding_owner_card_mul_le_selectedEdgeCopyPairsOutsideCurrent_ownerEdge_card_mul
        G A m e0 owner base hbase)
      hβ

set_option linter.style.longLine false in

theorem beta_mul_edgeCopySourceSectorContaining_incrementInserted_excluding_owner_card_mul_le_selectedEdgeCopyPairsOutsideCurrent_card_mul_of_ownerEdge_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 ew : ↥G.edgeFinset)
    (owner : Sharpness.FluxEdgeCopy.Copy G
      (Function.update m e0 (m e0 + 1)))
    (hownerEdge : owner.1 = ew) (β base : ℝ)
    (hβ : 0 ≤ β) (hbase : 0 ≤ base) :
    β *
        (((edgeCopySourceSectorContainingAndExcludingCopy G A
          (Function.update m e0 (m e0 + 1))
          (edgeCopyIncrementInserted G m e0) owner).card : ℝ) * base) ≤
      β *
        (((edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A
          (Function.update m e0 (m e0 + 1)) ew).card : ℝ) * base) := by
  rw [← hownerEdge]
  exact
    beta_mul_edgeCopySourceSectorContaining_incrementInserted_excluding_owner_card_mul_le_selectedEdgeCopyPairsOutsideCurrent_ownerEdge_card_mul
      G A m e0 owner β base hβ hbase

set_option linter.style.longLine false in


theorem edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_card_le_owner_incrementInserted_add_ownerEdgeOutsideCurrent_of_update_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (hmzero : m e0 = 0)
    (owner : Sharpness.FluxEdgeCopy.Copy G
      (Function.update m e0 (m e0 + 1))) :
    (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A
        (Function.update m e0 (m e0 + 1)) e0).card ≤
      (edgeCopySourceSectorContainingBothCopies G A
        (Function.update m e0 (m e0 + 1)) owner
        (edgeCopyIncrementInserted G m e0)).card +
      (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A
        (Function.update m e0 (m e0 + 1)) owner.1).card := by
  rw [
    edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_card_eq_owner_incrementInserted_add_incrementInserted_excluding_owner_of_update_zero
      G A m e0 hmzero owner]
  exact
    Nat.add_le_add_left
      (edgeCopySourceSectorContaining_incrementInserted_excluding_owner_card_le_selectedEdgeCopyPairsOutsideCurrent_ownerEdge_card
        G A m e0 owner)
      _

set_option linter.style.longLine false in


theorem edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_card_le_owner_incrementInserted_add_outsideCurrent_of_update_zero_ownerEdge_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 ew : ↥G.edgeFinset)
    (hmzero : m e0 = 0)
    (owner : Sharpness.FluxEdgeCopy.Copy G
      (Function.update m e0 (m e0 + 1)))
    (hownerEdge : owner.1 = ew) :
    (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A
        (Function.update m e0 (m e0 + 1)) e0).card ≤
      (edgeCopySourceSectorContainingBothCopies G A
        (Function.update m e0 (m e0 + 1)) owner
        (edgeCopyIncrementInserted G m e0)).card +
      (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A
        (Function.update m e0 (m e0 + 1)) ew).card := by
  rw [← hownerEdge]
  exact
    edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_card_le_owner_incrementInserted_add_ownerEdgeOutsideCurrent_of_update_zero
      G A m e0 hmzero owner

set_option linter.style.longLine false in


theorem edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_card_mul_le_owner_incrementInserted_add_ownerEdgeOutsideCurrent_card_mul_of_update_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (hmzero : m e0 = 0)
    (owner : Sharpness.FluxEdgeCopy.Copy G
      (Function.update m e0 (m e0 + 1))) (base : ℝ)
    (hbase : 0 ≤ base) :
    ((edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A
        (Function.update m e0 (m e0 + 1)) e0).card : ℝ) * base ≤
      ((edgeCopySourceSectorContainingBothCopies G A
        (Function.update m e0 (m e0 + 1)) owner
        (edgeCopyIncrementInserted G m e0)).card : ℝ) * base +
      ((edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A
        (Function.update m e0 (m e0 + 1)) owner.1).card : ℝ) * base := by
  have hcard_nat :=
    edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_card_le_owner_incrementInserted_add_ownerEdgeOutsideCurrent_of_update_zero
      G A m e0 hmzero owner
  have hcard_real :
      ((edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A
          (Function.update m e0 (m e0 + 1)) e0).card : ℝ) ≤
        ((edgeCopySourceSectorContainingBothCopies G A
          (Function.update m e0 (m e0 + 1)) owner
          (edgeCopyIncrementInserted G m e0)).card +
          (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A
            (Function.update m e0 (m e0 + 1)) owner.1).card : ℝ) := by
    exact_mod_cast hcard_nat
  calc
    ((edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A
        (Function.update m e0 (m e0 + 1)) e0).card : ℝ) * base ≤
      (((edgeCopySourceSectorContainingBothCopies G A
        (Function.update m e0 (m e0 + 1)) owner
        (edgeCopyIncrementInserted G m e0)).card +
        (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A
          (Function.update m e0 (m e0 + 1)) owner.1).card : ℝ) * base) :=
        mul_le_mul_of_nonneg_right hcard_real hbase
    _ =
      ((edgeCopySourceSectorContainingBothCopies G A
        (Function.update m e0 (m e0 + 1)) owner
        (edgeCopyIncrementInserted G m e0)).card : ℝ) * base +
      ((edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A
        (Function.update m e0 (m e0 + 1)) owner.1).card : ℝ) * base := by
        norm_num [Nat.cast_add, add_mul]

set_option linter.style.longLine false in


theorem edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_card_mul_le_owner_incrementInserted_add_outsideCurrent_card_mul_of_update_zero_ownerEdge_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 ew : ↥G.edgeFinset)
    (hmzero : m e0 = 0)
    (owner : Sharpness.FluxEdgeCopy.Copy G
      (Function.update m e0 (m e0 + 1)))
    (hownerEdge : owner.1 = ew) (base : ℝ) (hbase : 0 ≤ base) :
    ((edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A
        (Function.update m e0 (m e0 + 1)) e0).card : ℝ) * base ≤
      ((edgeCopySourceSectorContainingBothCopies G A
        (Function.update m e0 (m e0 + 1)) owner
        (edgeCopyIncrementInserted G m e0)).card : ℝ) * base +
      ((edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A
        (Function.update m e0 (m e0 + 1)) ew).card : ℝ) * base := by
  rw [← hownerEdge]
  exact
    edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_card_mul_le_owner_incrementInserted_add_ownerEdgeOutsideCurrent_card_mul_of_update_zero
      G A m e0 hmzero owner base hbase

set_option linter.style.longLine false in


theorem beta_mul_edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_card_mul_le_owner_incrementInserted_add_ownerEdgeOutsideCurrent_card_mul_of_update_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (hmzero : m e0 = 0)
    (owner : Sharpness.FluxEdgeCopy.Copy G
      (Function.update m e0 (m e0 + 1))) (β base : ℝ)
    (hβ : 0 ≤ β) (hbase : 0 ≤ base) :
    β *
        (((edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A
          (Function.update m e0 (m e0 + 1)) e0).card : ℝ) * base) ≤
      β *
          (((edgeCopySourceSectorContainingBothCopies G A
            (Function.update m e0 (m e0 + 1)) owner
            (edgeCopyIncrementInserted G m e0)).card : ℝ) * base) +
        β *
          (((edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A
            (Function.update m e0 (m e0 + 1)) owner.1).card : ℝ) * base) := by
  have hsplit :=
    edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_card_mul_le_owner_incrementInserted_add_ownerEdgeOutsideCurrent_card_mul_of_update_zero
      G A m e0 hmzero owner base hbase
  calc
    β *
        (((edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A
          (Function.update m e0 (m e0 + 1)) e0).card : ℝ) * base) ≤
      β *
        ((((edgeCopySourceSectorContainingBothCopies G A
          (Function.update m e0 (m e0 + 1)) owner
          (edgeCopyIncrementInserted G m e0)).card : ℝ) * base) +
          (((edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A
            (Function.update m e0 (m e0 + 1)) owner.1).card : ℝ) * base)) :=
        mul_le_mul_of_nonneg_left hsplit hβ
    _ =
      β *
          (((edgeCopySourceSectorContainingBothCopies G A
            (Function.update m e0 (m e0 + 1)) owner
            (edgeCopyIncrementInserted G m e0)).card : ℝ) * base) +
        β *
          (((edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A
            (Function.update m e0 (m e0 + 1)) owner.1).card : ℝ) * base) := by
        ring

set_option linter.style.longLine false in


theorem beta_mul_edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_card_mul_le_owner_incrementInserted_add_outsideCurrent_card_mul_of_update_zero_ownerEdge_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 ew : ↥G.edgeFinset)
    (hmzero : m e0 = 0)
    (owner : Sharpness.FluxEdgeCopy.Copy G
      (Function.update m e0 (m e0 + 1)))
    (hownerEdge : owner.1 = ew) (β base : ℝ)
    (hβ : 0 ≤ β) (hbase : 0 ≤ base) :
    β *
        (((edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A
          (Function.update m e0 (m e0 + 1)) e0).card : ℝ) * base) ≤
      β *
          (((edgeCopySourceSectorContainingBothCopies G A
            (Function.update m e0 (m e0 + 1)) owner
            (edgeCopyIncrementInserted G m e0)).card : ℝ) * base) +
        β *
          (((edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A
            (Function.update m e0 (m e0 + 1)) ew).card : ℝ) * base) := by
  rw [← hownerEdge]
  exact
    beta_mul_edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_card_mul_le_owner_incrementInserted_add_ownerEdgeOutsideCurrent_card_mul_of_update_zero
      G A m e0 hmzero owner β base hβ hbase

set_option linter.style.longLine false in


theorem edgeCopySourceSectorContaining_incrementInserted_excluding_owner_mem_selectedEdgeCopyPairsOutsideCurrent_selectedEdge_of_ownerEdge_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (owner : Sharpness.FluxEdgeCopy.Copy G
      (Function.update m e0 (m e0 + 1)))
    (hownerEdge : owner.1 = e0)
    {K : Finset (Sharpness.FluxEdgeCopy.Copy G
      (Function.update m e0 (m e0 + 1)))}
    (hK :
      K ∈ edgeCopySourceSectorContainingAndExcludingCopy G A
        (Function.update m e0 (m e0 + 1))
        (edgeCopyIncrementInserted G m e0) owner) :
    (⟨K, owner⟩ :
        Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G
          (Function.update m e0 (m e0 + 1))) =>
          Sharpness.FluxEdgeCopy.Copy G
            (Function.update m e0 (m e0 + 1)))) ∈
      edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A
        (Function.update m e0 (m e0 + 1)) e0 := by
  exact
    edgeCopySourceSectorContaining_incrementInserted_excluding_owner_mem_selectedEdgeCopyPairsOutsideCurrent_of_ownerEdge_eq
      G A m e0 e0 owner hownerEdge hK

set_option linter.style.longLine false in


theorem edgeCopySourceSectorContaining_incrementInserted_excluding_owner_card_le_selectedEdgeCopyPairsOutsideCurrent_selectedEdge_card_of_ownerEdge_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (owner : Sharpness.FluxEdgeCopy.Copy G
      (Function.update m e0 (m e0 + 1)))
    (hownerEdge : owner.1 = e0) :
    (edgeCopySourceSectorContainingAndExcludingCopy G A
        (Function.update m e0 (m e0 + 1))
        (edgeCopyIncrementInserted G m e0) owner).card ≤
      (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A
        (Function.update m e0 (m e0 + 1)) e0).card := by
  exact
    edgeCopySourceSectorContaining_incrementInserted_excluding_owner_card_le_selectedEdgeCopyPairsOutsideCurrent_card_of_ownerEdge_eq
      G A m e0 e0 owner hownerEdge

set_option linter.style.longLine false in


theorem edgeCopySourceSectorContaining_incrementInserted_excluding_owner_card_mul_le_selectedEdgeCopyPairsOutsideCurrent_selectedEdge_card_mul_of_ownerEdge_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (owner : Sharpness.FluxEdgeCopy.Copy G
      (Function.update m e0 (m e0 + 1)))
    (hownerEdge : owner.1 = e0) (base : ℝ) (hbase : 0 ≤ base) :
    ((edgeCopySourceSectorContainingAndExcludingCopy G A
        (Function.update m e0 (m e0 + 1))
        (edgeCopyIncrementInserted G m e0) owner).card : ℝ) * base ≤
      ((edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A
        (Function.update m e0 (m e0 + 1)) e0).card : ℝ) * base := by
  exact
    edgeCopySourceSectorContaining_incrementInserted_excluding_owner_card_mul_le_selectedEdgeCopyPairsOutsideCurrent_card_mul_of_ownerEdge_eq
      G A m e0 e0 owner hownerEdge base hbase

set_option linter.style.longLine false in


theorem beta_mul_edgeCopySourceSectorContaining_incrementInserted_excluding_owner_card_mul_le_selectedEdgeCopyPairsOutsideCurrent_selectedEdge_card_mul_of_ownerEdge_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (owner : Sharpness.FluxEdgeCopy.Copy G
      (Function.update m e0 (m e0 + 1)))
    (hownerEdge : owner.1 = e0) (β base : ℝ)
    (hβ : 0 ≤ β) (hbase : 0 ≤ base) :
    β *
        (((edgeCopySourceSectorContainingAndExcludingCopy G A
          (Function.update m e0 (m e0 + 1))
          (edgeCopyIncrementInserted G m e0) owner).card : ℝ) * base) ≤
      β *
        (((edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A
          (Function.update m e0 (m e0 + 1)) e0).card : ℝ) * base) := by
  exact
    beta_mul_edgeCopySourceSectorContaining_incrementInserted_excluding_owner_card_mul_le_selectedEdgeCopyPairsOutsideCurrent_card_mul_of_ownerEdge_eq
      G A m e0 e0 owner hownerEdge β base hβ hbase

set_option linter.style.longLine false in


theorem edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_card_le_owner_incrementInserted_add_selectedEdgeOutsideCurrent_of_update_zero_ownerEdge_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (hmzero : m e0 = 0)
    (owner : Sharpness.FluxEdgeCopy.Copy G
      (Function.update m e0 (m e0 + 1)))
    (hownerEdge : owner.1 = e0) :
    (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A
        (Function.update m e0 (m e0 + 1)) e0).card ≤
      (edgeCopySourceSectorContainingBothCopies G A
        (Function.update m e0 (m e0 + 1)) owner
        (edgeCopyIncrementInserted G m e0)).card +
      (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A
        (Function.update m e0 (m e0 + 1)) e0).card := by
  exact
    edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_card_le_owner_incrementInserted_add_outsideCurrent_of_update_zero_ownerEdge_eq
      G A m e0 e0 hmzero owner hownerEdge

set_option linter.style.longLine false in


theorem edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_card_mul_le_owner_incrementInserted_add_selectedEdgeOutsideCurrent_card_mul_of_update_zero_ownerEdge_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (hmzero : m e0 = 0)
    (owner : Sharpness.FluxEdgeCopy.Copy G
      (Function.update m e0 (m e0 + 1)))
    (hownerEdge : owner.1 = e0) (base : ℝ) (hbase : 0 ≤ base) :
    ((edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A
        (Function.update m e0 (m e0 + 1)) e0).card : ℝ) * base ≤
      ((edgeCopySourceSectorContainingBothCopies G A
        (Function.update m e0 (m e0 + 1)) owner
        (edgeCopyIncrementInserted G m e0)).card : ℝ) * base +
      ((edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A
        (Function.update m e0 (m e0 + 1)) e0).card : ℝ) * base := by
  exact
    edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_card_mul_le_owner_incrementInserted_add_outsideCurrent_card_mul_of_update_zero_ownerEdge_eq
      G A m e0 e0 hmzero owner hownerEdge base hbase

set_option linter.style.longLine false in


theorem beta_mul_edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_card_mul_le_owner_incrementInserted_add_selectedEdgeOutsideCurrent_card_mul_of_update_zero_ownerEdge_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (hmzero : m e0 = 0)
    (owner : Sharpness.FluxEdgeCopy.Copy G
      (Function.update m e0 (m e0 + 1)))
    (hownerEdge : owner.1 = e0) (β base : ℝ)
    (hβ : 0 ≤ β) (hbase : 0 ≤ base) :
    β *
        (((edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A
          (Function.update m e0 (m e0 + 1)) e0).card : ℝ) * base) ≤
      β *
          (((edgeCopySourceSectorContainingBothCopies G A
            (Function.update m e0 (m e0 + 1)) owner
            (edgeCopyIncrementInserted G m e0)).card : ℝ) * base) +
        β *
          (((edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A
            (Function.update m e0 (m e0 + 1)) e0).card : ℝ) * base) := by
  exact
    beta_mul_edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_card_mul_le_owner_incrementInserted_add_outsideCurrent_card_mul_of_update_zero_ownerEdge_eq
      G A m e0 e0 hmzero owner hownerEdge β base hβ hbase

set_option linter.style.longLine false in


theorem edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_card_mul_le_owner_incrementInserted_add_outsideCurrent_budget_of_update_zero_ownerEdge_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 ew : ↥G.edgeFinset)
    (hmzero : m e0 = 0)
    (owner : Sharpness.FluxEdgeCopy.Copy G
      (Function.update m e0 (m e0 + 1)))
    (hownerEdge : owner.1 = ew)
    (base ownerBudget outsideBudget : ℝ) (hbase : 0 ≤ base)
    (hownerBudget :
      ((edgeCopySourceSectorContainingBothCopies G A
        (Function.update m e0 (m e0 + 1)) owner
        (edgeCopyIncrementInserted G m e0)).card : ℝ) * base ≤
        ownerBudget)
    (houtsideBudget :
      ((edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A
        (Function.update m e0 (m e0 + 1)) ew).card : ℝ) * base ≤
        outsideBudget) :
    ((edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A
        (Function.update m e0 (m e0 + 1)) e0).card : ℝ) * base ≤
      ownerBudget + outsideBudget :=
  (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_card_mul_le_owner_incrementInserted_add_outsideCurrent_card_mul_of_update_zero_ownerEdge_eq
    G A m e0 ew hmzero owner hownerEdge base hbase).trans
    (add_le_add hownerBudget houtsideBudget)

set_option linter.style.longLine false in


theorem edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_card_mul_le_owner_incrementInserted_add_selectedEdgeOutsideCurrent_budget_of_update_zero_ownerEdge_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (hmzero : m e0 = 0)
    (owner : Sharpness.FluxEdgeCopy.Copy G
      (Function.update m e0 (m e0 + 1)))
    (hownerEdge : owner.1 = e0)
    (base ownerBudget outsideBudget : ℝ) (hbase : 0 ≤ base)
    (hownerBudget :
      ((edgeCopySourceSectorContainingBothCopies G A
        (Function.update m e0 (m e0 + 1)) owner
        (edgeCopyIncrementInserted G m e0)).card : ℝ) * base ≤
        ownerBudget)
    (houtsideBudget :
      ((edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A
        (Function.update m e0 (m e0 + 1)) e0).card : ℝ) * base ≤
        outsideBudget) :
    ((edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A
        (Function.update m e0 (m e0 + 1)) e0).card : ℝ) * base ≤
      ownerBudget + outsideBudget :=
  edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_card_mul_le_owner_incrementInserted_add_outsideCurrent_budget_of_update_zero_ownerEdge_eq
    G A m e0 e0 hmzero owner hownerEdge base ownerBudget outsideBudget
    hbase hownerBudget houtsideBudget

set_option linter.style.longLine false in


theorem beta_mul_edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_card_mul_le_owner_incrementInserted_add_outsideCurrent_budget_of_update_zero_ownerEdge_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 ew : ↥G.edgeFinset)
    (hmzero : m e0 = 0)
    (owner : Sharpness.FluxEdgeCopy.Copy G
      (Function.update m e0 (m e0 + 1)))
    (hownerEdge : owner.1 = ew)
    (β base ownerBudget outsideBudget : ℝ)
    (hβ : 0 ≤ β) (hbase : 0 ≤ base)
    (hownerBudget :
      β *
          (((edgeCopySourceSectorContainingBothCopies G A
            (Function.update m e0 (m e0 + 1)) owner
            (edgeCopyIncrementInserted G m e0)).card : ℝ) * base) ≤
        ownerBudget)
    (houtsideBudget :
      β *
          (((edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A
            (Function.update m e0 (m e0 + 1)) ew).card : ℝ) * base) ≤
        outsideBudget) :
    β *
        (((edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A
          (Function.update m e0 (m e0 + 1)) e0).card : ℝ) * base) ≤
      ownerBudget + outsideBudget :=
  (beta_mul_edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_card_mul_le_owner_incrementInserted_add_outsideCurrent_card_mul_of_update_zero_ownerEdge_eq
    G A m e0 ew hmzero owner hownerEdge β base hβ hbase).trans
    (add_le_add hownerBudget houtsideBudget)

set_option linter.style.longLine false in


theorem beta_mul_edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_card_mul_le_owner_incrementInserted_add_selectedEdgeOutsideCurrent_budget_of_update_zero_ownerEdge_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (hmzero : m e0 = 0)
    (owner : Sharpness.FluxEdgeCopy.Copy G
      (Function.update m e0 (m e0 + 1)))
    (hownerEdge : owner.1 = e0)
    (β base ownerBudget outsideBudget : ℝ)
    (hβ : 0 ≤ β) (hbase : 0 ≤ base)
    (hownerBudget :
      β *
          (((edgeCopySourceSectorContainingBothCopies G A
            (Function.update m e0 (m e0 + 1)) owner
            (edgeCopyIncrementInserted G m e0)).card : ℝ) * base) ≤
        ownerBudget)
    (houtsideBudget :
      β *
          (((edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A
            (Function.update m e0 (m e0 + 1)) e0).card : ℝ) * base) ≤
        outsideBudget) :
    β *
        (((edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A
          (Function.update m e0 (m e0 + 1)) e0).card : ℝ) * base) ≤
      ownerBudget + outsideBudget :=
  beta_mul_edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_card_mul_le_owner_incrementInserted_add_outsideCurrent_budget_of_update_zero_ownerEdge_eq
    G A m e0 e0 hmzero owner hownerEdge β base ownerBudget outsideBudget
    hβ hbase hownerBudget houtsideBudget


theorem edgeCopyIncrementMap_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset) :
    Function.Injective (edgeCopyIncrementMap G m e0) := by
  classical
  intro i j hij
  have hedge : i.1 = j.1 := by
    have hi := edgeCopyIncrementMap_fst G m e0 i
    have hj := edgeCopyIncrementMap_fst G m e0 j
    exact hi.symm.trans ((congrArg Sigma.fst hij).trans hj)
  rcases i with ⟨e, k⟩
  rcases j with ⟨f, l⟩
  simp only at hedge
  subst f
  by_cases he : e = e0
  · subst e
    have hidx :
        (⟨k.val, by rw [Function.update_self]; omega⟩ :
          Fin (Function.update m e0 (m e0 + 1) e0)) =
        (⟨l.val, by rw [Function.update_self]; omega⟩ :
          Fin (Function.update m e0 (m e0 + 1) e0)) := by
      simpa [edgeCopyIncrementMap] using hij
    have hkl : k = l := by
      apply Fin.ext
      have hv : k.val = l.val := by
        simpa using
          congrArg
            (fun z : Fin (Function.update m e0 (m e0 + 1) e0) => z.val)
            hidx
      exact hv
    cases hkl
    rfl
  · have hupdate : Function.update m e0 (m e0 + 1) e = m e := by
      rw [Function.update_of_ne he]
    have hidx : Fin.cast hupdate.symm k = Fin.cast hupdate.symm l := by
      simpa [edgeCopyIncrementMap, he, hupdate] using hij
    have hkl : k = l := by
      apply Fin.ext
      have hv := congrArg Fin.val hidx
      simpa [Fin.cast] using hv
    cases hkl
    rfl


theorem edgeCopyIncrementMap_ne_inserted
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (i : Sharpness.FluxEdgeCopy.Copy G m) :
    edgeCopyIncrementMap G m e0 i ≠ edgeCopyIncrementInserted G m e0 := by
  classical
  rcases i with ⟨e, k⟩
  by_cases he : e = e0
  · subst e
    intro h
    have hidx :
        (⟨k.val, by rw [Function.update_self]; omega⟩ :
          Fin (Function.update m e0 (m e0 + 1) e0)) =
        (⟨m e0, by rw [Function.update_self]; omega⟩ :
          Fin (Function.update m e0 (m e0 + 1) e0)) := by
      simpa [edgeCopyIncrementMap, edgeCopyIncrementInserted] using h
    have hv : k.val = m e0 := by
      simpa using
        congrArg
          (fun z : Fin (Function.update m e0 (m e0 + 1) e0) => z.val)
          hidx
    exact Nat.ne_of_lt k.isLt hv
  · intro h
    have hfst := congrArg Sigma.fst h
    have hedge : e = e0 := by
      simp [edgeCopyIncrementMap, edgeCopyIncrementInserted, he] at hfst
    exact he hedge


theorem edgeCopyIncrement_univ
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset) :
    insert (edgeCopyIncrementInserted G m e0)
        ((Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)).image
          (edgeCopyIncrementMap G m e0)) =
      (Finset.univ :
        Finset
          (Sharpness.FluxEdgeCopy.Copy G
            (Function.update m e0 (m e0 + 1)))) := by
  classical
  ext x
  simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and,
    iff_true]
  rcases x with ⟨e, k⟩
  by_cases he : e = e0
  · subst e
    by_cases hk : k.val = m e0
    · left
      have hidx : k = (⟨m e0, by rw [Function.update_self]; omega⟩ :
          Fin (Function.update m e0 (m e0 + 1) e0)) := by
        apply Fin.ext
        exact hk
      simp [edgeCopyIncrementInserted, hidx]
    · right
      have hklt : k.val < m e0 := by
        have hklt_succ : k.val < m e0 + 1 := by
          simpa [Function.update_self] using k.isLt
        omega
      refine ⟨⟨e0, ⟨k.val, hklt⟩⟩, ?_⟩
      have hidx : (⟨k.val, k.isLt⟩ :
          Fin (Function.update m e0 (m e0 + 1) e0)) = k := by
        apply Fin.ext
        rfl
      simp [edgeCopyIncrementMap, hidx]
  · right
    have hupdate : Function.update m e0 (m e0 + 1) e = m e := by
      rw [Function.update_of_ne he]
    refine ⟨⟨e, Fin.cast hupdate k⟩, ?_⟩
    simp [edgeCopyIncrementMap, he, Fin.cast]


theorem edgeMultiplicityIncrement_injective
    {ι : Type*} [DecidableEq ι] (e0 : ι) :
    Function.Injective
      (fun m : ι → ℕ => Function.update m e0 (m e0 + 1)) := by
  intro m₁ m₂ h
  funext e
  by_cases he : e = e0
  · subst e
    have hcoord := congrFun h e0
    simp [Function.update_self] at hcoord
    omega
  · have hcoord := congrFun h e
    simpa [Function.update_of_ne he] using hcoord


theorem edgeMultiplicityIncrement_decrement_eq
    {ι : Type*} [DecidableEq ι] (m : ι → ℕ) (e0 : ι) :
    Function.update (Function.update m e0 (m e0 + 1)) e0
      ((Function.update m e0 (m e0 + 1)) e0 - 1) = m := by
  funext e
  by_cases h : e = e0
  · subst e
    simp
  · simp [Function.update_of_ne h]

open Classical in
set_option linter.style.longLine false in


theorem edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_decrement_increment_profile_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V)
    {e0 : ↥G.edgeFinset}
    {m : ↥G.edgeFinset → ℕ}
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G
        (Function.update m e0 (m e0 + 1))) =>
      Sharpness.FluxEdgeCopy.Copy G (Function.update m e0 (m e0 + 1)))}
    (hp :
      p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A
        (Function.update m e0 (m e0 + 1)) e0) :
    Function.update (Function.update m e0 (m e0 + 1)) p.2.1
        ((Function.update m e0 (m e0 + 1)) p.2.1 - 1) = m := by
  classical
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  have hpbranch :=
    (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_mem
      (G := G) (A := A) (m := M) (e0 := e0) p).mp (by simpa [M] using hp)
  have hpbase :=
    (edgeCopySourceSectorSelectedEdgeCopyPairs_mem
      (G := G) (A := A) (m := M) (e0 := e0) p).mp hpbranch.1
  have hselected : p.2.1 = e0 := hpbase.2
  rw [hselected]
  exact edgeMultiplicityIncrement_decrement_eq m e0

open Classical in
set_option linter.style.longLine false in


theorem edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_decrement_increment_profile_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V)
    {e0 : ↥G.edgeFinset}
    {m : ↥G.edgeFinset → ℕ}
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G
        (Function.update m e0 (m e0 + 1))) =>
      Sharpness.FluxEdgeCopy.Copy G (Function.update m e0 (m e0 + 1)))}
    (hp :
      p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A
        (Function.update m e0 (m e0 + 1)) e0) :
    Function.update (Function.update m e0 (m e0 + 1)) p.2.1
        ((Function.update m e0 (m e0 + 1)) p.2.1 - 1) = m := by
  classical
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  have hpbranch :=
    (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_mem
      (G := G) (A := A) (m := M) (e0 := e0) p).mp (by simpa [M] using hp)
  have hpbase :=
    (edgeCopySourceSectorSelectedEdgeCopyPairs_mem
      (G := G) (A := A) (m := M) (e0 := e0) p).mp hpbranch.1
  have hselected : p.2.1 = e0 := hpbase.2
  rw [hselected]
  exact edgeMultiplicityIncrement_decrement_eq m e0

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsInCurrent_decrementMultiplicityIndex_edgeIncrement_fiber_card_eq_branch_card
    {n : ℕ} {w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    ((doubledBox_selectedEdgeCopyPairsInCurrent_decrementMultiplicityIndex
        (n := n) (w := w) (Function.update m e0 (m e0 + 1)) e0).fiber m).card =
      (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w)
        (Function.update m e0 (m e0 + 1)) e0).card := by
  classical
  let M : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ :=
    Function.update m e0 (m e0 + 1)
  let I :=
    doubledBox_selectedEdgeCopyPairsInCurrent_decrementMultiplicityIndex
      (n := n) (w := w) M e0
  have hfiber : I.fiber m = I.domain := by
    ext a
    rw [FinsetFiberIndex.mem_fiber]
    constructor
    · exact And.left
    · intro ha
      refine ⟨ha, ?_⟩
      have hpbranch :=
        (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_mem
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w) M e0 a.1).mp a.2
      have hbase :=
        (edgeCopySourceSectorSelectedEdgeCopyPairs_mem
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w) M e0 a.1).mp hpbranch.1
      have hpe : a.1.2.1 = e0 := hbase.2
      change Function.update M a.1.2.1 (M a.1.2.1 - 1) = m
      rw [hpe]
      simp [M]
  calc
    ((doubledBox_selectedEdgeCopyPairsInCurrent_decrementMultiplicityIndex
        (n := n) (w := w) (Function.update m e0 (m e0 + 1)) e0).fiber m).card =
        (I.fiber m).card := by rfl
    _ = I.domain.card := by rw [hfiber]
    _ = (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w)
          (Function.update m e0 (m e0 + 1)) e0).card := by
        simp [I, M, doubledBox_selectedEdgeCopyPairsInCurrent_decrementMultiplicityIndex,
          Finset.card_attach]

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsOutsideCurrent_decrementMultiplicityIndex_edgeIncrement_fiber_card_eq_branch_card
    {n : ℕ} {w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    ((doubledBox_selectedEdgeCopyPairsOutsideCurrent_decrementMultiplicityIndex
        (n := n) (w := w) (Function.update m e0 (m e0 + 1)) e0).fiber m).card =
      (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w)
        (Function.update m e0 (m e0 + 1)) e0).card := by
  classical
  let M : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ :=
    Function.update m e0 (m e0 + 1)
  let I :=
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_decrementMultiplicityIndex
      (n := n) (w := w) M e0
  have hfiber : I.fiber m = I.domain := by
    ext a
    rw [FinsetFiberIndex.mem_fiber]
    constructor
    · exact And.left
    · intro ha
      refine ⟨ha, ?_⟩
      have hpbranch :=
        (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_mem
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w) M e0 a.1).mp a.2
      have hbase :=
        (edgeCopySourceSectorSelectedEdgeCopyPairs_mem
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w) M e0 a.1).mp hpbranch.1
      have hpe : a.1.2.1 = e0 := hbase.2
      change Function.update M a.1.2.1 (M a.1.2.1 - 1) = m
      rw [hpe]
      simp [M]
  calc
    ((doubledBox_selectedEdgeCopyPairsOutsideCurrent_decrementMultiplicityIndex
        (n := n) (w := w) (Function.update m e0 (m e0 + 1)) e0).fiber m).card =
        (I.fiber m).card := by rfl
    _ = I.domain.card := by rw [hfiber]
    _ = (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w)
          (Function.update m e0 (m e0 + 1)) e0).card := by
        simp [I, M, doubledBox_selectedEdgeCopyPairsOutsideCurrent_decrementMultiplicityIndex,
          Finset.card_attach]


end Exact3D
end StatMech

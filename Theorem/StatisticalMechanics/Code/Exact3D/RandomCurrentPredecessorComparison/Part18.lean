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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part17
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

theorem edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G m) =>
      Sharpness.FluxEdgeCopy.Copy G m)) :
    p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A m e0 ↔
      p ∈ edgeCopySourceSectorSelectedEdgeCopyPairs G A m e0 ∧ p.2 ∈ p.1 := by
  classical
  simp [edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent]


theorem edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G m) =>
      Sharpness.FluxEdgeCopy.Copy G m)) :
    p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A m e0 ↔
      p ∈ edgeCopySourceSectorSelectedEdgeCopyPairs G A m e0 ∧ p.2 ∉ p.1 := by
  classical
  simp [edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent]

set_option linter.style.longLine false in


theorem edgeCopySourceSectorSelectedEdgeCopyPairs_selectedCopy_eq_inserted_of_update_zero
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
    p.2 =
      (⟨e0, ⟨0, by simp [hmzero]⟩⟩ :
        Sharpness.FluxEdgeCopy.Copy G
          (Function.update m e0 (m e0 + 1))) := by
  classical
  have hpedge :
      p.2.1 = e0 :=
    (edgeCopySourceSectorSelectedEdgeCopyPairs_mem
      (G := G) (A := A) (m := Function.update m e0 (m e0 + 1))
      (e0 := e0) (p := p)).mp hp |>.2
  rcases p with ⟨K, i⟩
  rcases i with ⟨e, j⟩
  dsimp at hpedge ⊢
  subst e
  congr
  apply Fin.ext
  have hjlt : (j : ℕ) < 1 := by
    simpa [Function.update, hmzero] using j.2
  have hjzero : (j : ℕ) = 0 := by omega
  simpa using hjzero

set_option linter.style.longLine false in


theorem edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_selectedCopy_eq_inserted_of_update_zero
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
    p.2 =
      (⟨e0, ⟨0, by simp [hmzero]⟩⟩ :
        Sharpness.FluxEdgeCopy.Copy G
          (Function.update m e0 (m e0 + 1))) :=
  edgeCopySourceSectorSelectedEdgeCopyPairs_selectedCopy_eq_inserted_of_update_zero
    G A m e0 hmzero
    ((edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_mem
      G A (Function.update m e0 (m e0 + 1)) e0 p).mp hp |>.1)

set_option linter.style.longLine false in


theorem edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_inserted_mem_of_update_zero
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
    (⟨e0, ⟨0, by simp [hmzero]⟩⟩ :
        Sharpness.FluxEdgeCopy.Copy G
          (Function.update m e0 (m e0 + 1))) ∈ p.1 := by
  classical
  have hpbranch :=
    (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_mem
      G A (Function.update m e0 (m e0 + 1)) e0 p).mp hp
  have hsel :=
    edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_selectedCopy_eq_inserted_of_update_zero
      G A m e0 hmzero hp
  simpa [hsel] using hpbranch.2

set_option linter.style.longLine false in


theorem edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_nonempty_of_fullSource_edge_pos
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G m)
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) =
        A)
    (hedge_pos : 0 < m e0) :
    (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A m e0).Nonempty := by
  classical
  let selected : Sharpness.FluxEdgeCopy.Copy G m := ⟨e0, ⟨0, hedge_pos⟩⟩
  let K : Finset (Sharpness.FluxEdgeCopy.Copy G m) := Finset.univ
  let p :
      Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G m) =>
        Sharpness.FluxEdgeCopy.Copy G m) := ⟨K, selected⟩
  refine ⟨p, ?_⟩
  exact
    (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_mem
      G A m e0 p).mpr
      ⟨(edgeCopySourceSectorSelectedEdgeCopyPairs_mem
          (G := G) (A := A) (m := m) (e0 := e0) (p := p)).mpr
          ⟨(mem_edgeCopySourceSector
              (G := G) (A := A) (m := m) (K := K)).mpr
              (by simpa [K] using hfull),
            by simp [p, selected]⟩,
        by simp [p, K, selected]⟩

set_option linter.style.longLine false in


theorem edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_card_pos_of_fullSource_edge_pos
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G m)
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) =
        A)
    (hedge_pos : 0 < m e0) :
    0 < (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A m e0).card :=
  Finset.Nonempty.card_pos
    (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_nonempty_of_fullSource_edge_pos
      G A m e0 hfull hedge_pos)

set_option linter.style.longLine false in


theorem edgeCopySourceSectorContainingCopy_card_le_selectedEdgeCopyPairs_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (owner selected : Sharpness.FluxEdgeCopy.Copy G m)
    (hselected_edge : selected.1 = e0) :
    (edgeCopySourceSectorContainingCopy G A m owner).card ≤
      (edgeCopySourceSectorSelectedEdgeCopyPairs G A m e0).card := by
  classical
  refine
    Finset.card_le_card_of_injOn
      (fun K : Finset (Sharpness.FluxEdgeCopy.Copy G m) =>
        (⟨K, selected⟩ :
          Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G m) =>
            Sharpness.FluxEdgeCopy.Copy G m))) ?_ ?_
  · intro K hK
    rcases
        (mem_edgeCopySourceSectorContainingCopy
          (G := G) (A := A) (m := m) (i := owner) (K := K)).mp hK with
      ⟨hKsource, _howner⟩
    exact
      (edgeCopySourceSectorSelectedEdgeCopyPairs_mem
        (G := G) (A := A) (m := m) (e0 := e0)
        (p :=
          (⟨K, selected⟩ :
            Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G m) =>
              Sharpness.FluxEdgeCopy.Copy G m)))).mpr
        ⟨hKsource, hselected_edge⟩
  · intro K _hK L _hL hmap
    exact congrArg Sigma.fst hmap

set_option linter.style.longLine false in


theorem edgeCopySourceSectorContainingBothCopies_card_le_selectedEdgeCopyPairsInCurrent_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (owner selected : Sharpness.FluxEdgeCopy.Copy G m)
    (hselected_edge : selected.1 = e0) :
    (edgeCopySourceSectorContainingBothCopies G A m owner selected).card ≤
      (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A m e0).card := by
  classical
  refine
    Finset.card_le_card_of_injOn
      (fun K : Finset (Sharpness.FluxEdgeCopy.Copy G m) =>
        (⟨K, selected⟩ :
          Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G m) =>
            Sharpness.FluxEdgeCopy.Copy G m))) ?_ ?_
  · intro K hK
    rcases
        (mem_edgeCopySourceSectorContainingBothCopies
          (G := G) (A := A) (m := m) (first := owner)
          (second := selected) (K := K)).mp hK with
      ⟨hKsource, _howner, hselected_mem⟩
    exact
      (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_mem
        G A m e0
        (⟨K, selected⟩ :
          Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G m) =>
            Sharpness.FluxEdgeCopy.Copy G m))).mpr
        ⟨(edgeCopySourceSectorSelectedEdgeCopyPairs_mem
            (G := G) (A := A) (m := m) (e0 := e0)
            (p :=
              (⟨K, selected⟩ :
                Sigma
                  (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G m) =>
                    Sharpness.FluxEdgeCopy.Copy G m)))).mpr
            ⟨hKsource, hselected_edge⟩,
          hselected_mem⟩
  · intro K _hK L _hL hmap
    exact congrArg Sigma.fst hmap

set_option linter.style.longLine false in


theorem edgeCopySourceSectorContainingAndExcludingCopy_card_le_selectedEdgeCopyPairsOutsideCurrent_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (inside outside : Sharpness.FluxEdgeCopy.Copy G m)
    (houtside_edge : outside.1 = e0) :
    (edgeCopySourceSectorContainingAndExcludingCopy G A m inside outside).card ≤
      (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A m e0).card := by
  classical
  refine
    Finset.card_le_card_of_injOn
      (fun K : Finset (Sharpness.FluxEdgeCopy.Copy G m) =>
        (⟨K, outside⟩ :
          Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G m) =>
            Sharpness.FluxEdgeCopy.Copy G m))) ?_ ?_
  · intro K hK
    rcases
        (mem_edgeCopySourceSectorContainingAndExcludingCopy
          (G := G) (A := A) (m := m) (inside := inside)
          (outside := outside) (K := K)).mp hK with
      ⟨hKsource, _hinside, houtside_not_mem⟩
    exact
      (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_mem
        G A m e0
        (⟨K, outside⟩ :
          Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G m) =>
            Sharpness.FluxEdgeCopy.Copy G m))).mpr
        ⟨(edgeCopySourceSectorSelectedEdgeCopyPairs_mem
            (G := G) (A := A) (m := m) (e0 := e0)
            (p :=
              (⟨K, outside⟩ :
                Sigma
                  (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G m) =>
                    Sharpness.FluxEdgeCopy.Copy G m)))).mpr
            ⟨hKsource, houtside_edge⟩,
          houtside_not_mem⟩
  · intro K _hK L _hL hmap
    exact congrArg Sigma.fst hmap

set_option linter.style.longLine false in


theorem edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_connK_univ_of_edge_eq_pair
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    {a b : V} (hab : a ≠ b) (hedge : e0.1 = s(a, b))
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G m) =>
      Sharpness.FluxEdgeCopy.Copy G m)}
    (hp : p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A m e0) :
    Sharpness.RandomCurrent.connK
      (Sharpness.FluxEdgeCopy.endsM G m)
      (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) a b := by
  have hpbase :=
    (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_mem G A m e0 p).mp hp
  exact edgeCopySourceSectorSelectedEdgeCopyPairs_connK_univ_of_edge_eq_pair
    G A m e0 hab hedge hpbase.1

set_option linter.style.longLine false in


theorem edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_connK_univ_of_edge_eq_pair
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    {a b : V} (hab : a ≠ b) (hedge : e0.1 = s(a, b))
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G m) =>
      Sharpness.FluxEdgeCopy.Copy G m)}
    (hp : p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A m e0) :
    Sharpness.RandomCurrent.connK
      (Sharpness.FluxEdgeCopy.endsM G m)
      (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) a b := by
  have hpbase :=
    (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_mem G A m e0 p).mp hp
  exact edgeCopySourceSectorSelectedEdgeCopyPairs_connK_univ_of_edge_eq_pair
    G A m e0 hab hedge hpbase.1

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpoint_connK_univ_of_selectedEdgeCopyPairInCurrent
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (A : Finset (FK.boxVerts 3 (2 * n)))
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
        (FK.boxGraph 3 (2 * n)) m) =>
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)}
    (hp :
      p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
        (FK.boxGraph 3 (2 * n)) A m e0) :
    Sharpness.RandomCurrent.connK
      (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
      (Finset.univ :
        Finset (Sharpness.FluxEdgeCopy.Copy
          (FK.boxGraph 3 (2 * n)) m))
      (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
      (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :=
  edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_connK_univ_of_edge_eq_pair
    (G := FK.boxGraph 3 (2 * n)) A m e0 hvw hedge hp

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpoint_connK_univ_of_selectedEdgeCopyPairOutsideCurrent
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (A : Finset (FK.boxVerts 3 (2 * n)))
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
        (FK.boxGraph 3 (2 * n)) m) =>
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)}
    (hp :
      p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n)) A m e0) :
    Sharpness.RandomCurrent.connK
      (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
      (Finset.univ :
        Finset (Sharpness.FluxEdgeCopy.Copy
          (FK.boxGraph 3 (2 * n)) m))
      (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
      (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :=
  edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_connK_univ_of_edge_eq_pair
    (G := FK.boxGraph 3 (2 * n)) A m e0 hvw hedge hp

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpointSourceSector_card_eq_of_selectedEdgeCopyPairInCurrent
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n v)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
        (FK.boxGraph 3 (2 * n)) m) =>
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)}
    (hp :
      p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v) m e0) :
    (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m).card =
      (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v) m).card := by
  have hpbase :=
    (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_mem
      (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n v) m e0 p).mp hp
  exact
    doubledBoxOriginToInnerEndpointSourceSector_card_eq_of_selectedEdgeCopyPair
      (n := n) (v := v) (w := w) m e0 hfull hedge hov how hvw hpbase.1

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpointSourceSector_card_eq_of_selectedEdgeCopyPairOutsideCurrent
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n v)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
        (FK.boxGraph 3 (2 * n)) m) =>
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)}
    (hp :
      p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v) m e0) :
    (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m).card =
      (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v) m).card := by
  have hpbase :=
    (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_mem
      (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n v) m e0 p).mp hp
  exact
    doubledBoxOriginToInnerEndpointSourceSector_card_eq_of_selectedEdgeCopyPair
      (n := n) (v := v) (w := w) m e0 hfull hedge hov how hvw hpbase.1

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpointSourceSector_reverse_card_eq_of_selectedEdgeCopyPairInCurrent
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n w)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
        (FK.boxGraph 3 (2 * n)) m) =>
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)}
    (hp :
      p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m e0) :
    (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v) m).card =
      (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m).card := by
  have hpbase :=
    (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_mem
      (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n w) m e0 p).mp hp
  exact
    doubledBoxOriginToInnerEndpointSourceSector_reverse_card_eq_of_selectedEdgeCopyPair
      (n := n) (v := v) (w := w) m e0 hfull hedge hov how hvw hpbase.1

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpointSourceSector_reverse_card_eq_of_selectedEdgeCopyPairOutsideCurrent
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n w)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
        (FK.boxGraph 3 (2 * n)) m) =>
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)}
    (hp :
      p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m e0) :
    (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v) m).card =
      (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m).card := by
  have hpbase :=
    (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_mem
      (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n w) m e0 p).mp hp
  exact
    doubledBoxOriginToInnerEndpointSourceSector_reverse_card_eq_of_selectedEdgeCopyPair
      (n := n) (v := v) (w := w) m e0 hfull hedge hov how hvw hpbase.1

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpointSourceSector_card_eq_of_selectedEdgeCopyPairsInCurrent_nonempty
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n v)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hne :
      (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v) m e0).Nonempty) :
    (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m).card =
      (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v) m).card := by
  rcases hne with ⟨p, hp⟩
  exact
    doubledBoxOriginToInnerEndpointSourceSector_card_eq_of_selectedEdgeCopyPairInCurrent
      (n := n) (v := v) (w := w) m e0 hfull hedge hov how hvw hp

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpointSourceSector_card_eq_of_selectedEdgeCopyPairsOutsideCurrent_nonempty
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n v)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hne :
      (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v) m e0).Nonempty) :
    (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m).card =
      (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v) m).card := by
  rcases hne with ⟨p, hp⟩
  exact
    doubledBoxOriginToInnerEndpointSourceSector_card_eq_of_selectedEdgeCopyPairOutsideCurrent
      (n := n) (v := v) (w := w) m e0 hfull hedge hov how hvw hp

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpointSourceSector_reverse_card_eq_of_selectedEdgeCopyPairsInCurrent_nonempty
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n w)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hne :
      (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m e0).Nonempty) :
    (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v) m).card =
      (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m).card := by
  rcases hne with ⟨p, hp⟩
  exact
    doubledBoxOriginToInnerEndpointSourceSector_reverse_card_eq_of_selectedEdgeCopyPairInCurrent
      (n := n) (v := v) (w := w) m e0 hfull hedge hov how hvw hp

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpointSourceSector_reverse_card_eq_of_selectedEdgeCopyPairsOutsideCurrent_nonempty
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n w)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hne :
      (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m e0).Nonempty) :
    (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v) m).card =
      (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m).card := by
  rcases hne with ⟨p, hp⟩
  exact
    doubledBoxOriginToInnerEndpointSourceSector_reverse_card_eq_of_selectedEdgeCopyPairOutsideCurrent
      (n := n) (v := v) (w := w) m e0 hfull hedge hov how hvw hp

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsInCurrent_card_le_switchedSourceSector_card_mul_succ
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n))
            (Function.update m e0 (m e0 + 1)))
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n))
              (Function.update m e0 (m e0 + 1)))) =
        doubledBoxOriginToInnerEndpointSource n w)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w)
        (Function.update m e0 (m e0 + 1)) e0).card ≤
      (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (Function.update m e0 (m e0 + 1))).card * (m e0 + 1) := by
  classical
  let G := FK.boxGraph 3 (2 * n)
  let A := doubledBoxOriginToInnerEndpointSource n w
  let B := doubledBoxOriginToInnerEndpointSource n v
  let M : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ :=
    Function.update m e0 (m e0 + 1)
  let S := edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A M e0
  let Sall := edgeCopySourceSectorSelectedEdgeCopyPairs G A M e0
  change S.card ≤ (edgeCopySourceSector G B M).card * (m e0 + 1)
  by_cases hne : S.Nonempty
  · have hswitch :
        (edgeCopySourceSector G B M).card =
          (edgeCopySourceSector G A M).card := by
      simpa [G, A, B, M] using
        doubledBoxOriginToInnerEndpointSourceSector_reverse_card_eq_of_selectedEdgeCopyPairsInCurrent_nonempty
          (n := n) (v := v) (w := w) M e0 hfull hedge hov how hvw
          (by simpa [S, G, A, M] using hne)
    have hsubset : S ⊆ Sall := by
      intro p hp
      exact
        (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_mem
          G A M e0 p).mp hp |>.1
    have hcard_le : S.card ≤ Sall.card :=
      Finset.card_le_card hsubset
    calc
      S.card ≤ Sall.card := hcard_le
      _ = (edgeCopySourceSector G A M).card * M e0 := by
        simpa [Sall] using
          edgeCopySourceSectorSelectedEdgeCopyPairs_card G A M e0
      _ = (edgeCopySourceSector G B M).card * (m e0 + 1) := by
        rw [← hswitch]
        simp [M]
  · have hempty : S = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact hne ⟨p, hp⟩
    rw [hempty]
    exact Nat.zero_le _

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsOutsideCurrent_card_le_switchedSourceSector_card_mul_succ
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n))
            (Function.update m e0 (m e0 + 1)))
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n))
              (Function.update m e0 (m e0 + 1)))) =
        doubledBoxOriginToInnerEndpointSource n w)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w)
        (Function.update m e0 (m e0 + 1)) e0).card ≤
      (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (Function.update m e0 (m e0 + 1))).card * (m e0 + 1) := by
  classical
  let G := FK.boxGraph 3 (2 * n)
  let A := doubledBoxOriginToInnerEndpointSource n w
  let B := doubledBoxOriginToInnerEndpointSource n v
  let M : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ :=
    Function.update m e0 (m e0 + 1)
  let S := edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A M e0
  let Sall := edgeCopySourceSectorSelectedEdgeCopyPairs G A M e0
  change S.card ≤ (edgeCopySourceSector G B M).card * (m e0 + 1)
  by_cases hne : S.Nonempty
  · have hswitch :
        (edgeCopySourceSector G B M).card =
          (edgeCopySourceSector G A M).card := by
      simpa [G, A, B, M] using
        doubledBoxOriginToInnerEndpointSourceSector_reverse_card_eq_of_selectedEdgeCopyPairsOutsideCurrent_nonempty
          (n := n) (v := v) (w := w) M e0 hfull hedge hov how hvw
          (by simpa [S, G, A, M] using hne)
    have hsubset : S ⊆ Sall := by
      intro p hp
      exact
        (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_mem
          G A M e0 p).mp hp |>.1
    have hcard_le : S.card ≤ Sall.card :=
      Finset.card_le_card hsubset
    calc
      S.card ≤ Sall.card := hcard_le
      _ = (edgeCopySourceSector G A M).card * M e0 := by
        simpa [Sall] using
          edgeCopySourceSectorSelectedEdgeCopyPairs_card G A M e0
      _ = (edgeCopySourceSector G B M).card * (m e0 + 1) := by
        rw [← hswitch]
        simp [M]
  · have hempty : S = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact hne ⟨p, hp⟩
    rw [hempty]
    exact Nat.zero_le _


theorem edgeCopySourceSectorSelectedEdgeCopyPairs_sum_eq_inCurrent_add_outside
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (F : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G m) =>
      Sharpness.FluxEdgeCopy.Copy G m) → ℝ) :
    (∑ p ∈ edgeCopySourceSectorSelectedEdgeCopyPairs G A m e0, F p) =
      (∑ p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A m e0,
        F p) +
        ∑ p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A m e0,
          F p := by
  classical
  let S := edgeCopySourceSectorSelectedEdgeCopyPairs G A m e0
  let P :
      Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G m) =>
        Sharpness.FluxEdgeCopy.Copy G m) → Prop :=
    fun p => p.2 ∈ p.1
  have h := Finset.sum_filter_add_sum_filter_not (s := S) (p := P) (f := F)
  dsimp [S, P] at h
  rw [edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent,
    edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent]
  exact h.symm

set_option linter.style.longLine false in


theorem edgeCopySourceSectorSelectedEdgeCopyPairs_branch_card_add_eq_total_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset) :
    (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A m e0).card +
      (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A m e0).card =
      (edgeCopySourceSectorSelectedEdgeCopyPairs G A m e0).card := by
  classical
  let S := edgeCopySourceSectorSelectedEdgeCopyPairs G A m e0
  let P :
      Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G m) =>
        Sharpness.FluxEdgeCopy.Copy G m) → Prop :=
    fun p => p.2 ∈ p.1
  have h := Finset.card_filter_add_card_filter_not (s := S) (p := P)
  change (S.filter P).card + (S.filter (fun p => ¬ P p)).card = S.card at h
  change
    (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A m e0).card +
      (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A m e0).card =
      S.card
  simpa [S, P, edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent,
    edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent] using h

set_option linter.style.longLine false in


theorem edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_card_eq_total_iff_inCurrent_card_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset) :
    (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A m e0).card =
        (edgeCopySourceSectorSelectedEdgeCopyPairs G A m e0).card ↔
      (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A m e0).card = 0 := by
  have hsplit :=
    edgeCopySourceSectorSelectedEdgeCopyPairs_branch_card_add_eq_total_card
      G A m e0
  constructor
  · intro houtside
    omega
  · intro hin
    omega

set_option linter.style.longLine false in


theorem edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_card_lt_total_iff_inCurrent_card_pos
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset) :
    (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A m e0).card <
        (edgeCopySourceSectorSelectedEdgeCopyPairs G A m e0).card ↔
      0 <
        (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A m e0).card := by
  have hsplit :=
    edgeCopySourceSectorSelectedEdgeCopyPairs_branch_card_add_eq_total_card
      G A m e0
  constructor
  · intro hlt
    omega
  · intro hin
    omega

set_option linter.style.longLine false in


theorem edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_card_pos_or_outsideCurrent_card_eq_total
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset) :
    0 < (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A m e0).card ∨
      (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A m e0).card =
        (edgeCopySourceSectorSelectedEdgeCopyPairs G A m e0).card := by
  by_cases hin :
      0 < (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A m e0).card
  · exact Or.inl hin
  · right
    exact
      (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_card_eq_total_iff_inCurrent_card_eq_zero
        G A m e0).mpr (by omega)

set_option linter.style.longLine false in


theorem edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_nonempty_or_outsideCurrent_card_eq_total
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset) :
    (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A m e0).Nonempty ∨
      (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A m e0).card =
        (edgeCopySourceSectorSelectedEdgeCopyPairs G A m e0).card := by
  rcases
      edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_card_pos_or_outsideCurrent_card_eq_total
        G A m e0 with hpos | hexhaust
  · exact Or.inl (Finset.card_pos.mp hpos)
  · exact Or.inr hexhaust

set_option linter.style.longLine false in


theorem edgeCopySourceSectorSelectedEdgeCopyPairs_branch_card_add_eq_sourceSector_card_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset) :
    (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A m e0).card +
      (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A m e0).card =
      (edgeCopySourceSector G A m).card * m e0 := by
  rw [edgeCopySourceSectorSelectedEdgeCopyPairs_branch_card_add_eq_total_card]
  exact edgeCopySourceSectorSelectedEdgeCopyPairs_card G A m e0


theorem edgeCopySourceSectorSelectedEdgeCopyPairs_edge_count_mul_term_eq_inCurrent_add_outside
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V)
    (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset) :
    ((m e0 : ℕ) : ℝ) * edgeCopySourcePairEmptyCollapsedTerm G β J A m =
      (if
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G m)
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) = A then
          ∑ _p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A m e0,
            Sharpness.weight G β J (Sharpness.ofEdgeFun G m)
        else
          0) +
      (if
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G m)
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) = A then
          ∑ _p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A m e0,
            Sharpness.weight G β J (Sharpness.ofEdgeFun G m)
        else
          0) := by
  classical
  by_cases hfull :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM G m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) = A
  · rw [if_pos hfull, if_pos hfull]
    rw [← edgeCopySourceSectorSelectedEdgeCopyPairs_sum_weight_eq_edge_count_mul_term_of_fullSource
      G β J A m e0 hfull]
    exact edgeCopySourceSectorSelectedEdgeCopyPairs_sum_eq_inCurrent_add_outside
      G A m e0 (fun _p => Sharpness.weight G β J (Sharpness.ofEdgeFun G m))
  · rw [edgeCopySourcePairEmptyCollapsedTerm_eq_zero_of_not_fullSource
      G β J A m hfull]
    simp [hfull]

end Exact3D
end StatMech

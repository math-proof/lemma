/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorRecovery
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitOrientedFourColor.Part3
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorSlots
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem colorClass_lpReplicaFourColorTransport
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (E : α ≃ β) (color : ↑(Finset.univ : Finset α) -> Fin 4)
    (a : Fin 4) :
    colorClass Finset.univ (lpReplicaFourColorTransport E color) a =
      (colorClass Finset.univ color a).map E.toEmbedding := by
  ext x
  simp [colorClass, lpReplicaFourColorTransport]


theorem rowClass_lpReplicaFourColorTransport
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (E : α ≃ β) (color : ↑(Finset.univ : Finset α) -> Fin 4)
    (r : Fin 2) :
    rowClass Finset.univ (lpReplicaFourColorTransport E color) r =
      (rowClass Finset.univ color r).map E.toEmbedding := by
  by_cases hr : r = 0
  · subst r
    rw [rowClass_zero, rowClass_zero,
      colorClass_lpReplicaFourColorTransport,
      colorClass_lpReplicaFourColorTransport, Finset.map_union]
  · have hr1 : r = 1 := by omega
    subst r
    rw [rowClass_one, rowClass_one,
      colorClass_lpReplicaFourColorTransport,
      colorClass_lpReplicaFourColorTransport, Finset.map_union]


theorem leftPattern_lpReplicaFourColorTransport
    {α β W : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] [Fintype W] [DecidableEq W]
    (E : α ≃ β) (endsα : α -> Sym2 W) (endsβ : β -> Sym2 W)
    (hends : forall x, endsβ (E x) = endsα x)
    (A B : Finset W) (u v : W)
    (color : ↑(Finset.univ : Finset α) -> Fin 4)
    (hleft : LeftPattern endsα Finset.univ A B u v color) :
    LeftPattern endsβ Finset.univ A B u v
      (lpReplicaFourColorTransport E color) := by
  rcases hleft with ⟨h0, h1, h2, h3, hd0, hd1⟩
  unfold LeftPattern RowsDisconnect
  rw [colorClass_lpReplicaFourColorTransport,
    colorClass_lpReplicaFourColorTransport,
    colorClass_lpReplicaFourColorTransport,
    colorClass_lpReplicaFourColorTransport,
    rowClass_lpReplicaFourColorTransport,
    rowClass_lpReplicaFourColorTransport]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [randomCurrent_sources_map_embedding
      endsα endsβ E.toEmbedding hends]
    exact h0
  · rw [randomCurrent_sources_map_embedding
      endsα endsβ E.toEmbedding hends]
    exact h1
  · rw [randomCurrent_sources_map_embedding
      endsα endsβ E.toEmbedding hends]
    exact h2
  · rw [randomCurrent_sources_map_embedding
      endsα endsβ E.toEmbedding hends]
    exact h3
  · intro huv
    exact hd0 ((randomCurrent_connK_map_embedding
      endsα endsβ E.toEmbedding hends _ u v).1 huv)
  · intro huv
    exact hd1 ((randomCurrent_connK_map_embedding
      endsα endsβ E.toEmbedding hends _ u v).1 huv)


theorem lpReplicaCurrentEdge_reflect_mem_strictReps_of_not_mem
    (G : SimpleGraph V) (sites : I -> V)
    (e : (lpReplicaCurrentGraph G sites).edgeFinset)
    (hfixed : e ∉ lpReplicaCurrentEdgeOrbitFixed G sites)
    (hstrict : e ∉ lpReplicaCurrentEdgeOrbitStrictReps G sites) :
    lpReplicaCurrentEdgeReflect G sites e ∈
      lpReplicaCurrentEdgeOrbitStrictReps G sites := by
  have hne : e ≠ lpReplicaCurrentEdgeReflect G sites e := by
    intro he
    exact hfixed ((mem_lpReplicaCurrentEdgeOrbitFixed G sites e).2 he)
  have hreflectRep : lpReplicaCurrentEdgeReflect G sites e ∈
      lpReplicaCurrentEdgeOrbitReps G sites := by
    rcases lpReplicaCurrentEdge_mem_reps_or_reflect_mem_reps
        G sites e with heRep | hreflectRep
    · exact False.elim (hstrict
        ((mem_lpReplicaCurrentEdgeOrbitStrictReps G sites e).2
          ⟨heRep, hne⟩))
    · exact hreflectRep
  rw [mem_lpReplicaCurrentEdgeOrbitStrictReps]
  refine ⟨hreflectRep, ?_⟩
  intro he
  apply hne
  change lpReplicaCurrentEdgeReflect G sites e =
    lpReplicaCurrentEdgeReflect G sites
      (lpReplicaCurrentEdgeReflect G sites e) at he
  exact (lpReplicaCurrentEdgeReflect G sites).injective he


end
end StatMech.Ising

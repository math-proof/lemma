/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCollisionResummation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaComponentReflection.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.BackbonePartialEdgeCopySwitching.Part6
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaCollisionResummation.Part7
open Finset


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaCollisionLeftCopyEmbedding_ends
    (G : SimpleGraph V) (sites : I -> V)
    (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) a) :
    StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites a b)
        (lpReplicaCollisionLeftCopyEmbedding G sites a b c) =
      StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites) a c := by
  rcases c with ⟨e, k⟩
  simp [lpReplicaCollisionLeftCopyEmbedding,
    StatMech.Sharpness.FluxEdgeCopy.endsM,
    lpReplicaCollisionCopyEquiv]

theorem lpReplicaCollisionRightCopyEmbedding_ends
    (G : SimpleGraph V) (sites : I -> V)
    (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) b) :
    StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites a b)
        (lpReplicaCollisionRightCopyEmbedding G sites a b c) =
      Sym2.map lpReplicaCurrentReflect
        (StatMech.Sharpness.FluxEdgeCopy.endsM
          (lpReplicaCurrentGraph G sites) b c) := by
  rcases c with ⟨e, k⟩
  simp [lpReplicaCollisionRightCopyEmbedding,
    StatMech.Sharpness.FluxEdgeCopy.endsM,
    lpReplicaCollisionCopyEquiv,
    lpReplicaReflectCopyEquiv]

theorem randomCurrent_sources_map_embedding
    {K L W : Type*} [Fintype W] [DecidableEq W]
    (endsK : K -> Sym2 W) (endsL : L -> Sym2 W)
    (f : K ↪ L) (hends : ∀ c, endsL (f c) = endsK c)
    (S : Finset K) :
    StatMech.Sharpness.RandomCurrent.sources endsL (S.map f) =
      StatMech.Sharpness.RandomCurrent.sources endsK S := by
  classical
  ext x
  simp only [StatMech.Sharpness.RandomCurrent.sources,
    Finset.mem_filter, Finset.mem_univ, true_and]
  unfold StatMech.Sharpness.RandomCurrent.degK
  rw [Finset.filter_map, Finset.card_map]
  have hfilter :
      S.filter ((fun i => x ∈ endsL i) ∘ f) =
        S.filter (fun i => x ∈ endsK i) := by
    apply Finset.filter_congr
    intro c _
    change x ∈ endsL (f c) ↔ x ∈ endsK c
    rw [hends c]
  rw [hfilter]

theorem randomCurrent_connK_map_embedding
    {K L W : Type*}
    (endsK : K -> Sym2 W) (endsL : L -> Sym2 W)
    (f : K ↪ L) (hends : ∀ c, endsL (f c) = endsK c)
    (S : Finset K) (u v : W) :
    StatMech.Sharpness.RandomCurrent.connK endsL (S.map f) u v ↔
      StatMech.Sharpness.RandomCurrent.connK endsK S u v := by
  classical
  have hadj : ∀ x y,
      StatMech.Sharpness.RandomCurrent.adjStep endsL (S.map f) x y ↔
        StatMech.Sharpness.RandomCurrent.adjStep endsK S x y := by
    intro x y
    constructor
    · rintro ⟨c, hc, hx, hy, hxy⟩
      simp only [Finset.mem_map] at hc
      rcases hc with ⟨d, hd, rfl⟩
      exact ⟨d, hd, hends d ▸ hx, hends d ▸ hy, hxy⟩
    · rintro ⟨c, hc, hx, hy, hxy⟩
      exact ⟨f c, Finset.mem_map.mpr ⟨c, hc, rfl⟩,
        hends c ▸ hx, hends c ▸ hy, hxy⟩
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail h hstep ih =>
        exact Relation.ReflTransGen.tail ih ((hadj _ _).1 hstep)
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail h hstep ih =>
        exact Relation.ReflTransGen.tail ih ((hadj _ _).2 hstep)


end
end StatMech.Ising

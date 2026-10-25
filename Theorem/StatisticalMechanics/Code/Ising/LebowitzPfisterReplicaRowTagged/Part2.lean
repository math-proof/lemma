/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaRowTagged.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaFourFunctions
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaRowTagged.Part2
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.RandomCurrent

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]

section CollisionTag

variable [Fintype I] [DecidableEq I]


theorem lpReplicaCollision_origin_disjoint
    (G : SimpleGraph V) (sites : I -> V)
    (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Disjoint
      ((Finset.univ : Finset
        (Copy (lpReplicaCurrentGraph G sites) a)).map
          (lpReplicaCollisionLeftCopyEmbedding G sites a b))
      ((Finset.univ : Finset
        (Copy (lpReplicaCurrentGraph G sites) b)).map
          (lpReplicaCollisionRightCopyEmbedding G sites a b)) := by
  rw [Finset.disjoint_left]
  intro c hcL hcR
  simp only [Finset.mem_map, Finset.mem_univ, true_and] at hcL hcR
  rcases hcL with ⟨l, rfl⟩
  rcases hcR with ⟨r, hr⟩
  have h := (lpReplicaCollisionCopyEquiv G sites a b).injective hr
  have hk := congrArg (fun z : LPReplicaCollisionCopy G sites a b =>
    match z.2 with
    | .inl _ => false
    | .inr _ => true) h
  simp at hk

theorem lpReplicaCollision_origin_union
    (G : SimpleGraph V) (sites : I -> V)
    (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    (Finset.univ : Finset
        (Copy (lpReplicaCurrentGraph G sites) a)).map
          (lpReplicaCollisionLeftCopyEmbedding G sites a b) ∪
      (Finset.univ : Finset
        (Copy (lpReplicaCurrentGraph G sites) b)).map
          (lpReplicaCollisionRightCopyEmbedding G sites a b) =
      Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro c
  generalize ho : (lpReplicaCollisionCopyEquiv G sites a b).symm c = o
  rcases o with ⟨e, k | k⟩
  · apply Finset.mem_union_left
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    refine ⟨⟨e, k⟩, ?_⟩
    change lpReplicaCollisionCopyEquiv G sites a b ⟨e, Sum.inl k⟩ = c
    rw [← ho, (lpReplicaCollisionCopyEquiv G sites a b).apply_symm_apply]
  · apply Finset.mem_union_right
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    let cr : Copy (lpReplicaCurrentGraph G sites)
        (fun f => b (lpReplicaCurrentEdgeReflect G sites f)) := ⟨e, k⟩
    let r := (lpReplicaReflectCopyEquiv G sites b).symm cr
    refine ⟨r, ?_⟩
    change lpReplicaCollisionCopyEquiv G sites a b
        ⟨(lpReplicaReflectCopyEquiv G sites b r).1,
          Sum.inr (lpReplicaReflectCopyEquiv G sites b r).2⟩ = c
    rw [(lpReplicaReflectCopyEquiv G sites b).apply_symm_apply cr]
    rw [← ho, (lpReplicaCollisionCopyEquiv G sites a b).apply_symm_apply]

theorem lpReplicaCollision_rightOrigin_eq_sdiff
    (G : SimpleGraph V) (sites : I -> V)
    (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    (Finset.univ : Finset
        (Copy (lpReplicaCurrentGraph G sites) b)).map
          (lpReplicaCollisionRightCopyEmbedding G sites a b) =
      Finset.univ \ ((Finset.univ : Finset
        (Copy (lpReplicaCurrentGraph G sites) a)).map
          (lpReplicaCollisionLeftCopyEmbedding G sites a b)) := by
  apply Finset.Subset.antisymm
  · intro c hc
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
      (Finset.disjoint_left.mp
        (lpReplicaCollision_origin_disjoint G sites a b).symm) hc⟩
  · intro c hc
    have hU := Finset.mem_union.mp
      (show c ∈
        (Finset.univ : Finset
          (Copy (lpReplicaCurrentGraph G sites) a)).map
            (lpReplicaCollisionLeftCopyEmbedding G sites a b) ∪
        (Finset.univ : Finset
          (Copy (lpReplicaCurrentGraph G sites) b)).map
            (lpReplicaCollisionRightCopyEmbedding G sites a b) by
        rw [lpReplicaCollision_origin_union]
        exact Finset.mem_univ c)
    exact hU.resolve_left (Finset.mem_sdiff.mp hc).2

theorem lpReplicaCollision_currentCopies_left_false
    (G : SimpleGraph V) (sites : I -> V)
    (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (Sa : Finset (Copy (lpReplicaCurrentGraph G sites) a))
    (Sb : Finset (Copy (lpReplicaCurrentGraph G sites) b)) :
    lpReplicaCurrentCopies G sites
        (lpReplicaCollisionProfile G sites a b)
        (lpReplicaCollisionRowTag G sites a b Sa Sb) false false =
      Sa.map (lpReplicaCollisionLeftCopyEmbedding G sites a b) := by
  ext c
  let L := (Finset.univ : Finset
    (Copy (lpReplicaCurrentGraph G sites) a)).map
      (lpReplicaCollisionLeftCopyEmbedding G sites a b)
  let S := Sa.map (lpReplicaCollisionLeftCopyEmbedding G sites a b)
  have hSL : S ⊆ L :=
    Finset.map_subset_map.mpr (Finset.subset_univ Sa)
  simp only [lpReplicaCurrentCopies, Finset.mem_filter,
    Finset.mem_univ, true_and]
  change lpReplicaCollisionRowTag G sites a b Sa Sb c = (false, false) ↔ c ∈ S
  change (if c ∈ L then
      (false, if c ∈ S then false else true)
    else
      (true, if c ∈ Sb.map
        (lpReplicaCollisionRightCopyEmbedding G sites a b) then false else true)) =
      (false, false) ↔ c ∈ S
  by_cases hcS : c ∈ S
  · simp [hcS, hSL hcS]
  · by_cases hcL : c ∈ L <;> simp [hcS, hcL]

theorem lpReplicaCollision_currentCopies_left_true
    (G : SimpleGraph V) (sites : I -> V)
    (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (Sa : Finset (Copy (lpReplicaCurrentGraph G sites) a))
    (Sb : Finset (Copy (lpReplicaCurrentGraph G sites) b)) :
    lpReplicaCurrentCopies G sites
        (lpReplicaCollisionProfile G sites a b)
        (lpReplicaCollisionRowTag G sites a b Sa Sb) false true =
      ((Finset.univ : Finset
        (Copy (lpReplicaCurrentGraph G sites) a)) \ Sa).map
          (lpReplicaCollisionLeftCopyEmbedding G sites a b) := by
  rw [Finset.map_sdiff]
  ext c
  let L := (Finset.univ : Finset
    (Copy (lpReplicaCurrentGraph G sites) a)).map
      (lpReplicaCollisionLeftCopyEmbedding G sites a b)
  let S := Sa.map (lpReplicaCollisionLeftCopyEmbedding G sites a b)
  simp only [lpReplicaCurrentCopies, Finset.mem_filter,
    Finset.mem_univ, true_and]
  change lpReplicaCollisionRowTag G sites a b Sa Sb c = (false, true) ↔
    c ∈ L \ S
  change (if c ∈ L then
      (false, if c ∈ S then false else true)
    else
      (true, if c ∈ Sb.map
        (lpReplicaCollisionRightCopyEmbedding G sites a b) then false else true)) =
      (false, true) ↔ c ∈ L \ S
  by_cases hcL : c ∈ L <;> by_cases hcS : c ∈ S <;>
    simp [hcL, hcS]

theorem lpReplicaCollision_currentCopies_right_false
    (G : SimpleGraph V) (sites : I -> V)
    (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (Sa : Finset (Copy (lpReplicaCurrentGraph G sites) a))
    (Sb : Finset (Copy (lpReplicaCurrentGraph G sites) b)) :
    lpReplicaCurrentCopies G sites
        (lpReplicaCollisionProfile G sites a b)
        (lpReplicaCollisionRowTag G sites a b Sa Sb) true false =
      Sb.map (lpReplicaCollisionRightCopyEmbedding G sites a b) := by
  ext c
  let L := (Finset.univ : Finset
    (Copy (lpReplicaCurrentGraph G sites) a)).map
      (lpReplicaCollisionLeftCopyEmbedding G sites a b)
  let S := Sa.map (lpReplicaCollisionLeftCopyEmbedding G sites a b)
  let U := Sb.map (lpReplicaCollisionRightCopyEmbedding G sites a b)
  have hUL : Disjoint U L :=
    (lpReplicaCollision_origin_disjoint G sites a b).symm.mono
      (Finset.map_subset_map.mpr (Finset.subset_univ Sb)) Finset.Subset.rfl
  simp only [lpReplicaCurrentCopies, Finset.mem_filter,
    Finset.mem_univ, true_and]
  change lpReplicaCollisionRowTag G sites a b Sa Sb c = (true, false) ↔ c ∈ U
  change (if c ∈ L then (false, if c ∈ S then false else true)
    else (true, if c ∈ U then false else true)) = (true, false) ↔ c ∈ U
  by_cases hcU : c ∈ U
  · have hcL : c ∉ L := Finset.disjoint_left.mp hUL hcU
    simp [hcU, hcL]
  · by_cases hcL : c ∈ L <;> simp [hcU, hcL]

theorem lpReplicaCollision_currentCopies_right_true
    (G : SimpleGraph V) (sites : I -> V)
    (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (Sa : Finset (Copy (lpReplicaCurrentGraph G sites) a))
    (Sb : Finset (Copy (lpReplicaCurrentGraph G sites) b)) :
    lpReplicaCurrentCopies G sites
        (lpReplicaCollisionProfile G sites a b)
        (lpReplicaCollisionRowTag G sites a b Sa Sb) true true =
      ((Finset.univ : Finset
        (Copy (lpReplicaCurrentGraph G sites) b)) \ Sb).map
          (lpReplicaCollisionRightCopyEmbedding G sites a b) := by
  rw [Finset.map_sdiff]
  ext c
  let L := (Finset.univ : Finset
    (Copy (lpReplicaCurrentGraph G sites) a)).map
      (lpReplicaCollisionLeftCopyEmbedding G sites a b)
  let S := Sa.map (lpReplicaCollisionLeftCopyEmbedding G sites a b)
  let R := (Finset.univ : Finset
    (Copy (lpReplicaCurrentGraph G sites) b)).map
      (lpReplicaCollisionRightCopyEmbedding G sites a b)
  let U := Sb.map (lpReplicaCollisionRightCopyEmbedding G sites a b)
  have hR : R = Finset.univ \ L :=
    lpReplicaCollision_rightOrigin_eq_sdiff G sites a b
  simp only [lpReplicaCurrentCopies, Finset.mem_filter,
    Finset.mem_univ, true_and]
  change lpReplicaCollisionRowTag G sites a b Sa Sb c = (true, true) ↔
    c ∈ R \ U
  change (if c ∈ L then (false, if c ∈ S then false else true)
    else (true, if c ∈ U then false else true)) = (true, true) ↔
      c ∈ R \ U
  rw [hR]
  by_cases hcL : c ∈ L <;> by_cases hcU : c ∈ U <;>
    simp [hcL, hcU]

theorem lpReplicaCollision_rowCopies_false
    (G : SimpleGraph V) (sites : I -> V)
    (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (Sa : Finset (Copy (lpReplicaCurrentGraph G sites) a))
    (Sb : Finset (Copy (lpReplicaCurrentGraph G sites) b)) :
    lpReplicaRowCopies G sites
        (lpReplicaCollisionProfile G sites a b)
        (lpReplicaCollisionRowTag G sites a b Sa Sb) false =
      (Finset.univ : Finset
        (Copy (lpReplicaCurrentGraph G sites) a)).map
          (lpReplicaCollisionLeftCopyEmbedding G sites a b) := by
  ext c
  let L := (Finset.univ : Finset
    (Copy (lpReplicaCurrentGraph G sites) a)).map
      (lpReplicaCollisionLeftCopyEmbedding G sites a b)
  let S := Sa.map (lpReplicaCollisionLeftCopyEmbedding G sites a b)
  simp only [lpReplicaRowCopies, Finset.mem_filter, Finset.mem_univ, true_and]
  change (lpReplicaCollisionRowTag G sites a b Sa Sb c).1 = false ↔ c ∈ L
  by_cases hcL : c ∈ L
  · have hcL' : c ∈ (Finset.univ : Finset
        (Copy (lpReplicaCurrentGraph G sites) a)).map
          (lpReplicaCollisionLeftCopyEmbedding G sites a b) := hcL
    simp [lpReplicaCollisionRowTag, hcL', hcL]
  · have hcL' : c ∉ (Finset.univ : Finset
        (Copy (lpReplicaCurrentGraph G sites) a)).map
          (lpReplicaCollisionLeftCopyEmbedding G sites a b) := hcL
    simp [lpReplicaCollisionRowTag, hcL', hcL]

theorem lpReplicaCollision_rowCopies_true
    (G : SimpleGraph V) (sites : I -> V)
    (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (Sa : Finset (Copy (lpReplicaCurrentGraph G sites) a))
    (Sb : Finset (Copy (lpReplicaCurrentGraph G sites) b)) :
    lpReplicaRowCopies G sites
        (lpReplicaCollisionProfile G sites a b)
        (lpReplicaCollisionRowTag G sites a b Sa Sb) true =
      (Finset.univ : Finset
        (Copy (lpReplicaCurrentGraph G sites) b)).map
          (lpReplicaCollisionRightCopyEmbedding G sites a b) := by
  rw [lpReplicaCollision_rightOrigin_eq_sdiff]
  ext c
  let L := (Finset.univ : Finset
    (Copy (lpReplicaCurrentGraph G sites) a)).map
      (lpReplicaCollisionLeftCopyEmbedding G sites a b)
  let S := Sa.map (lpReplicaCollisionLeftCopyEmbedding G sites a b)
  simp only [lpReplicaRowCopies, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_sdiff]
  change (lpReplicaCollisionRowTag G sites a b Sa Sb c).1 = true ↔ c ∉ L
  by_cases hcL : c ∈ L
  · have hcL' : c ∈ (Finset.univ : Finset
        (Copy (lpReplicaCurrentGraph G sites) a)).map
          (lpReplicaCollisionLeftCopyEmbedding G sites a b) := hcL
    simp [lpReplicaCollisionRowTag, hcL', hcL]
  · have hcL' : c ∉ (Finset.univ : Finset
        (Copy (lpReplicaCurrentGraph G sites) a)).map
          (lpReplicaCollisionLeftCopyEmbedding G sites a b) := hcL
    simp [lpReplicaCollisionRowTag, hcL', hcL]

theorem lpReplicaCollision_leftSources
    (G : SimpleGraph V) (sites : I -> V)
    (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (Sa : Finset (Copy (lpReplicaCurrentGraph G sites) a))
    (Sb : Finset (Copy (lpReplicaCurrentGraph G sites) b))
    (current : Bool) :
    RandomCurrent.sources
        (endsM (lpReplicaCurrentGraph G sites)
          (lpReplicaCollisionProfile G sites a b))
        (lpReplicaCurrentCopies G sites
          (lpReplicaCollisionProfile G sites a b)
          (lpReplicaCollisionRowTag G sites a b Sa Sb) false current) =
      RandomCurrent.sources
        (endsM (lpReplicaCurrentGraph G sites) a)
        (if current then Finset.univ \ Sa else Sa) := by
  cases current
  · rw [lpReplicaCollision_currentCopies_left_false]
    exact randomCurrent_sources_map_embedding _ _ _
      (lpReplicaCollisionLeftCopyEmbedding_ends G sites a b) Sa
  · rw [lpReplicaCollision_currentCopies_left_true]
    exact randomCurrent_sources_map_embedding _ _ _
      (lpReplicaCollisionLeftCopyEmbedding_ends G sites a b)
      (Finset.univ \ Sa)

theorem lpReplicaCollision_rightSources
    (G : SimpleGraph V) (sites : I -> V)
    (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (Sa : Finset (Copy (lpReplicaCurrentGraph G sites) a))
    (Sb : Finset (Copy (lpReplicaCurrentGraph G sites) b))
    (current : Bool) :
    RandomCurrent.sources
        (endsM (lpReplicaCurrentGraph G sites)
          (lpReplicaCollisionProfile G sites a b))
        (lpReplicaCurrentCopies G sites
          (lpReplicaCollisionProfile G sites a b)
          (lpReplicaCollisionRowTag G sites a b Sa Sb) true current) =
      (RandomCurrent.sources
        (endsM (lpReplicaCurrentGraph G sites) b)
        (if current then Finset.univ \ Sb else Sb)).map
          lpReplicaCurrentReflect.toEmbedding := by
  have hsource (T : Finset (Copy (lpReplicaCurrentGraph G sites) b)) :
      RandomCurrent.sources
          (endsM (lpReplicaCurrentGraph G sites)
            (lpReplicaCollisionProfile G sites a b))
          (T.map (lpReplicaCollisionRightCopyEmbedding G sites a b)) =
        (RandomCurrent.sources
          (endsM (lpReplicaCurrentGraph G sites) b) T).map
            lpReplicaCurrentReflect.toEmbedding := by
    calc
      RandomCurrent.sources
          (endsM (lpReplicaCurrentGraph G sites)
            (lpReplicaCollisionProfile G sites a b))
          (T.map (lpReplicaCollisionRightCopyEmbedding G sites a b)) =
        RandomCurrent.sources
          (fun c => Sym2.map lpReplicaCurrentReflect
            (endsM (lpReplicaCurrentGraph G sites) b c)) T :=
          randomCurrent_sources_map_embedding _ _ _
            (lpReplicaCollisionRightCopyEmbedding_ends G sites a b) T
      _ = RandomCurrent.sources
          (endsM (lpReplicaCurrentGraph G sites)
            (fun e => b (lpReplicaCurrentEdgeReflect G sites e)))
          (lpReplicaReflectCopies G sites b T) := by
          symm
          exact randomCurrent_sources_map_embedding _ _ _
            (lpReplicaReflectCopyEquiv_ends G sites b) T
      _ = (RandomCurrent.sources
          (endsM (lpReplicaCurrentGraph G sites) b) T).map
            lpReplicaCurrentReflect.toEmbedding :=
          lpReplicaReflectCopies_sources G sites b T
  cases current
  · rw [lpReplicaCollision_currentCopies_right_false]
    exact hsource Sb
  · rw [lpReplicaCollision_currentCopies_right_true]
    exact hsource (Finset.univ \ Sb)

end CollisionTag
end
end StatMech.Ising

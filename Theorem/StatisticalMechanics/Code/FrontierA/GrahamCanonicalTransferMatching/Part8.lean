/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferComponentCut.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Def.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferMatching.Part8
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalMaskRightSecondRows_collision_or_equiv
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (c : ↑S)
    (f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S)
    (hf : CanonicalMaskRightAugmentedMatching
      ends m j k l zero p S c f)
    (s : {u : ↑S // u ≠ c} ->
      ↑(canonicalMaskRightNeighborhood ends m j k l zero p S))
    (hne : ∀ u, s u ≠ canonicalMaskRightAugmentedAssignedImage
      ends m j k l zero p S c f hf u.1 u.2) :
    (∃ u v, u ≠ v ∧ s u = s v) ∨
      ∃ e : {u : ↑S // u ≠ c} ≃
          ↑(canonicalMaskRightNeighborhood ends m j k l zero p S),
        (∀ u, e u = s u) ∧
        ∀ u, e u ≠ canonicalMaskRightAugmentedAssignedImage
          ends m j k l zero p S c f hf u.1 u.2 := by
  classical
  by_cases hinj : Function.Injective s
  · right
    have hcard : Fintype.card {u : ↑S // u ≠ c} =
        Fintype.card ↑(canonicalMaskRightNeighborhood
          ends m j k l zero p S) :=
      Fintype.card_congr (canonicalMaskRightAugmentedAssignedEquiv
        ends m j k l zero p S c f hf)
    have hbij : Function.Bijective s :=
      (Fintype.bijective_iff_injective_and_card s).mpr ⟨hinj, hcard⟩
    let e := Equiv.ofBijective s hbij
    exact ⟨e, fun _ => rfl, hne⟩
  · left
    obtain ⟨u, v, huv, huvne⟩ := Function.not_injective_iff.mp hinj
    exact ⟨u, v, huvne, huv⟩


theorem canonicalMaskRightFullSecondRows_repetition_or_equiv
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (c : ↑S)
    (f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S)
    (hf : CanonicalMaskRightAugmentedMatching
      ends m j k l zero p S c f)
    (hsecond : ∀ u : {u : ↑S // u ≠ c},
      ∃ r : ↑(canonicalMaskRightNeighborhood ends m j k l zero p S),
        r ≠ canonicalMaskRightAugmentedAssignedImage
          ends m j k l zero p S c f hf u.1 u.2 ∧
        r.1 ∈ canonicalMaskRightImages ends m j k l zero p u.1.1) :
    (∃ u v : {u : ↑S // u ≠ c},
        ∃ r : ↑(canonicalMaskRightNeighborhood ends m j k l zero p S),
          u ≠ v ∧
          r ≠ canonicalMaskRightAugmentedAssignedImage
            ends m j k l zero p S c f hf u.1 u.2 ∧
          r ≠ canonicalMaskRightAugmentedAssignedImage
            ends m j k l zero p S c f hf v.1 v.2 ∧
          r.1 ∈ canonicalMaskRightImages ends m j k l zero p u.1.1 ∧
          r.1 ∈ canonicalMaskRightImages ends m j k l zero p v.1.1) ∨
      ∃ e : {u : ↑S // u ≠ c} ≃
          ↑(canonicalMaskRightNeighborhood ends m j k l zero p S),
        ∀ u,
          e u ≠ canonicalMaskRightAugmentedAssignedImage
            ends m j k l zero p S c f hf u.1 u.2 ∧
          (e u).1 ∈ canonicalMaskRightImages
            ends m j k l zero p u.1.1 := by
  classical
  let s : {u : ↑S // u ≠ c} ->
      ↑(canonicalMaskRightNeighborhood ends m j k l zero p S) := fun u =>
    (hsecond u).choose
  have hs : ∀ u,
      s u ≠ canonicalMaskRightAugmentedAssignedImage
          ends m j k l zero p S c f hf u.1 u.2 ∧
        (s u).1 ∈ canonicalMaskRightImages
          ends m j k l zero p u.1.1 := fun u => (hsecond u).choose_spec
  rcases canonicalMaskRightSecondRows_collision_or_equiv
      ends m j k l zero p S c f hf s (fun u => (hs u).1) with
    hrepeat | hequiv
  · left
    obtain ⟨u, v, huv, hsuv⟩ := hrepeat
    refine ⟨u, v, s u, huv, (hs u).1, ?_, (hs u).2, ?_⟩
    · rw [hsuv]
      exact (hs v).1
    · rw [hsuv]
      exact (hs v).2
  · right
    obtain ⟨e, he, hene⟩ := hequiv
    refine ⟨e, ?_⟩
    intro u
    refine ⟨hene u, ?_⟩
    rw [he u]
    exact (hs u).2


theorem canonicalMaskRightSecondRowEquiv_collisionPerm
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (c : ↑S)
    (f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S)
    (hf : CanonicalMaskRightAugmentedMatching
      ends m j k l zero p S c f)
    (e : {u : ↑S // u ≠ c} ≃
      ↑(canonicalMaskRightNeighborhood ends m j k l zero p S))
    (hene : ∀ u, e u ≠ canonicalMaskRightAugmentedAssignedImage
      ends m j k l zero p S c f hf u.1 u.2)
    (hemem : ∀ u, (e u).1 ∈ canonicalMaskRightImages
      ends m j k l zero p u.1.1) :
    ∃ τ : Equiv.Perm {u : ↑S // u ≠ c},
      (∀ u, τ u ≠ u) ∧
      ∀ u,
        (e u).1 ∈ canonicalMaskRightImages
            ends m j k l zero p u.1.1 ∧
          (e u).1 ∈ canonicalMaskRightImages
            ends m j k l zero p (τ u).1.1 := by
  let base := canonicalMaskRightAugmentedAssignedEquiv
    ends m j k l zero p S c f hf
  let τ : Equiv.Perm {u : ↑S // u ≠ c} := e.trans base.symm
  refine ⟨τ, ?_, ?_⟩
  · intro u hfix
    apply hene u
    calc
      e u = base (τ u) := by simp [τ, base]
      _ = base u := congrArg base hfix
      _ = canonicalMaskRightAugmentedAssignedImage
          ends m j k l zero p S c f hf u.1 u.2 := rfl
  · intro u
    refine ⟨hemem u, ?_⟩
    have hbase : base (τ u) = e u := by simp [τ, base]
    have hmem := canonicalMaskRightAugmentedAssignedImage_mem
      ends m j k l zero p S c f hf (τ u).1 (τ u).2
    change (base (τ u)).1 ∈ canonicalMaskRightImages
      ends m j k l zero p (τ u).1.1 at hmem
    rwa [hbase] at hmem


theorem canonicalMaskRightRepeatedSecondRow_threePreimages
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (c : ↑S)
    (f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S)
    (hf : CanonicalMaskRightAugmentedMatching
      ends m j k l zero p S c f)
    (u v : {u : ↑S // u ≠ c})
    (r : ↑(canonicalMaskRightNeighborhood ends m j k l zero p S))
    (huv : u ≠ v)
    (hru : r ≠ canonicalMaskRightAugmentedAssignedImage
      ends m j k l zero p S c f hf u.1 u.2)
    (hrv : r ≠ canonicalMaskRightAugmentedAssignedImage
      ends m j k l zero p S c f hf v.1 v.2)
    (hruMem : r.1 ∈ canonicalMaskRightImages
      ends m j k l zero p u.1.1)
    (hrvMem : r.1 ∈ canonicalMaskRightImages
      ends m j k l zero p v.1.1) :
    ∃ w : {u : ↑S // u ≠ c},
      u ≠ v ∧ w ≠ u ∧ w ≠ v ∧
      r.1 ∈ canonicalMaskRightImages ends m j k l zero p u.1.1 ∧
      r.1 ∈ canonicalMaskRightImages ends m j k l zero p v.1.1 ∧
      r.1 ∈ canonicalMaskRightImages ends m j k l zero p w.1.1 := by
  let base := canonicalMaskRightAugmentedAssignedEquiv
    ends m j k l zero p S c f hf
  let w : {u : ↑S // u ≠ c} := base.symm r
  have hbase : base w = r := by simp [w]
  have hwu : w ≠ u := by
    intro h
    apply hru
    calc
      r = base w := hbase.symm
      _ = base u := congrArg base h
      _ = canonicalMaskRightAugmentedAssignedImage
          ends m j k l zero p S c f hf u.1 u.2 := rfl
  have hwv : w ≠ v := by
    intro h
    apply hrv
    calc
      r = base w := hbase.symm
      _ = base v := congrArg base h
      _ = canonicalMaskRightAugmentedAssignedImage
          ends m j k l zero p S c f hf v.1 v.2 := rfl
  have hrw := canonicalMaskRightAugmentedAssignedImage_mem
    ends m j k l zero p S c f hf w.1 w.2
  change (base w).1 ∈ canonicalMaskRightImages
    ends m j k l zero p w.1.1 at hrw
  rw [hbase] at hrw
  exact ⟨w, huv, hwu, hwv, hruMem, hrvMem, hrw⟩


end StatMech.GrahamGHS.FourColor

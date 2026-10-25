/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferComponentCut.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Def.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferMatching.Part5
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalMaskRightHall_iff_exists_matching
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    CanonicalMaskRightHall ends m j k l zero p ↔
      ∃ f : leftMaskFiber ends m j k l zero p ↪
          rightMaskFiber ends m j k l zero p,
        ∀ c, f c ∈ canonicalMaskRightImages ends m j k l zero p c := by
  classical
  let rel := fun c : leftMaskFiber ends m j k l zero p =>
    fun q : rightMaskFiber ends m j k l zero p =>
      q ∈ canonicalMaskRightImages ends m j k l zero p c
  have hhall := Fintype.all_card_le_filter_rel_iff_exists_injective rel
  constructor
  · intro h
    have h' : ∀ S : Finset (leftMaskFiber ends m j k l zero p),
        S.card ≤ (Finset.univ.filter fun q =>
          ∃ c ∈ S, rel c q).card := by
      simpa only [CanonicalMaskRightHall,
        canonicalMaskRightNeighborhood] using h
    obtain ⟨f, hf, himage⟩ := hhall.mp h'
    exact ⟨⟨f, hf⟩, himage⟩
  · rintro ⟨f, himage⟩
    have h' : ∀ S : Finset (leftMaskFiber ends m j k l zero p),
        S.card ≤ (Finset.univ.filter fun q =>
          ∃ c ∈ S, rel c q).card :=
      hhall.mpr ⟨f, f.injective, himage⟩
    simpa only [CanonicalMaskRightHall,
      canonicalMaskRightNeighborhood] using h'


theorem GrahamFiberMinor_of_canonicalMaskRightHall
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hhall : ∀ p : Finset I × Finset I,
      CanonicalMaskRightHall ends m j k l zero p) :
    GrahamFiberMinor ends m j k l zero := by
  apply GrahamFiberMinor_of_maskFiberEmbeddings
  intro p
  exact Classical.choose
    ((canonicalMaskRightHall_iff_exists_matching
      ends m j k l zero p).mp (hhall p))


theorem canonicalMaskRightNeighborhood_mono
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    {S T : Finset (leftMaskFiber ends m j k l zero p)}
    (hST : S ⊆ T) :
    canonicalMaskRightNeighborhood ends m j k l zero p S ⊆
      canonicalMaskRightNeighborhood ends m j k l zero p T := by
  intro q hq
  obtain ⟨c, hcS, hqc⟩ := (mem_canonicalMaskRightNeighborhood_iff
    ends m j k l zero p S q).mp hq
  exact (mem_canonicalMaskRightNeighborhood_iff
    ends m j k l zero p T q).mpr ⟨c, hST hcS, hqc⟩


theorem exists_other_of_erase_canonicalMaskRightNeighborhood_eq
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (c : leftMaskFiber ends m j k l zero p) (hc : c ∈ S)
    (herase : canonicalMaskRightNeighborhood
        ends m j k l zero p (S.erase c) =
      canonicalMaskRightNeighborhood ends m j k l zero p S)
    (q : rightMaskFiber ends m j k l zero p)
    (hqc : q ∈ canonicalMaskRightImages ends m j k l zero p c) :
    ∃ d ∈ S, d ≠ c ∧
      q ∈ canonicalMaskRightImages ends m j k l zero p d := by
  classical
  have hqS : q ∈ canonicalMaskRightNeighborhood
      ends m j k l zero p S :=
    (mem_canonicalMaskRightNeighborhood_iff
      ends m j k l zero p S q).mpr ⟨c, hc, hqc⟩
  have hqErase : q ∈ canonicalMaskRightNeighborhood
      ends m j k l zero p (S.erase c) := by
    rw [herase]
    exact hqS
  obtain ⟨d, hdErase, hqd⟩ :=
    (mem_canonicalMaskRightNeighborhood_iff
      ends m j k l zero p (S.erase c) q).mp hqErase
  have hd := Finset.mem_erase.mp hdErase
  exact ⟨d, hd.2, hd.1, hqd⟩


theorem exists_other_mem_canonicalWorkingTranslatedRows_of_erase_eq
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (c : leftMaskFiber ends m j k l zero p) (hc : c ∈ S)
    (herase : canonicalMaskRightNeighborhood
        ends m j k l zero p (S.erase c) =
      canonicalMaskRightNeighborhood ends m j k l zero p S)
    (K : Finset I)
    (hK : K ∈ canonicalWorkingTranslatedRows
      ends m j k l zero p c) :
    ∃ d ∈ S, d ≠ c ∧ K ∈ canonicalWorkingTranslatedRows
      ends m j k l zero p d := by
  classical
  rw [← image_rowClass_zero_canonicalMaskRightImages
    ends m j k l zero hloop hjk hkl p c] at hK
  obtain ⟨q, hqc, hrow⟩ := Finset.mem_image.mp hK
  obtain ⟨d, hdS, hdc, hqd⟩ :=
    exists_other_of_erase_canonicalMaskRightNeighborhood_eq
      ends m j k l zero p S c hc herase q hqc
  refine ⟨d, hdS, hdc, ?_⟩
  rw [← image_rowClass_zero_canonicalMaskRightImages
    ends m j k l zero hloop hjk hkl p d]
  exact Finset.mem_image.mpr ⟨q, hqd, hrow⟩


theorem exists_canonicalMaskRightMatching_of_properHall
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (hproper : ∀ T : Finset (leftMaskFiber ends m j k l zero p),
      T ⊂ S -> T.card ≤
        (canonicalMaskRightNeighborhood ends m j k l zero p T).card)
    (c : leftMaskFiber ends m j k l zero p) (hc : c ∈ S) :
    ∃ f : ↑(S.erase c) ↪ rightMaskFiber ends m j k l zero p,
      ∀ x, f x ∈ canonicalMaskRightImages ends m j k l zero p x.1 := by
  classical
  let rel := fun x : ↑(S.erase c) =>
    fun q : rightMaskFiber ends m j k l zero p =>
      q ∈ canonicalMaskRightImages ends m j k l zero p x.1
  have hHall : ∀ A : Finset ↑(S.erase c), A.card ≤
      (Finset.univ.filter fun q => ∃ x ∈ A, rel x q).card := by
    intro A
    let T := A.image fun x => x.1
    have hTS : T ⊆ S := by
      intro x hx
      obtain ⟨y, hyA, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_erase.mp y.2).2
    have hcT : c ∉ T := by
      intro h
      obtain ⟨y, -, hy⟩ := Finset.mem_image.mp h
      exact (Finset.mem_erase.mp y.2).1 hy
    have hTproper : T ⊂ S :=
      Finset.ssubset_iff_subset_ne.mpr
        ⟨hTS, fun hTS' => hcT (hTS' ▸ hc)⟩
    have hcardA : A.card = T.card :=
      (Finset.card_image_of_injective A Subtype.val_injective).symm
    have hneighborhood :
        (Finset.univ.filter fun q => ∃ x ∈ A, rel x q) =
          canonicalMaskRightNeighborhood ends m j k l zero p T := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        mem_canonicalMaskRightNeighborhood_iff, T, rel]
      constructor
      · rintro ⟨x, hxA, hqx⟩
        exact ⟨x.1, Finset.mem_image.mpr ⟨x, hxA, rfl⟩, hqx⟩
      · rintro ⟨x, hxT, hqx⟩
        obtain ⟨y, hyA, hy⟩ := Finset.mem_image.mp hxT
        exact ⟨y, hyA, hy ▸ hqx⟩
    rw [hcardA, hneighborhood]
    exact hproper T hTproper
  obtain ⟨f, hf, himage⟩ :=
    (Fintype.all_card_le_filter_rel_iff_exists_injective rel).mp hHall
  exact ⟨⟨f, hf⟩, himage⟩


theorem exists_canonicalMaskRightNearPerfectEquiv
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (htight : (canonicalMaskRightNeighborhood
        ends m j k l zero p S).card + 1 = S.card)
    (hproper : ∀ T : Finset (leftMaskFiber ends m j k l zero p),
      T ⊂ S -> T.card ≤
        (canonicalMaskRightNeighborhood ends m j k l zero p T).card)
    (c : leftMaskFiber ends m j k l zero p) (hc : c ∈ S) :
    ∃ f : ↑(S.erase c) ≃
        ↑(canonicalMaskRightNeighborhood ends m j k l zero p S),
      ∀ x, (f x).1 ∈ canonicalMaskRightImages
        ends m j k l zero p x.1 := by
  classical
  obtain ⟨f, hf⟩ := exists_canonicalMaskRightMatching_of_properHall
    ends m j k l zero p S hproper c hc
  let g : ↑(S.erase c) ->
      ↑(canonicalMaskRightNeighborhood ends m j k l zero p S) :=
    fun x => ⟨f x, (mem_canonicalMaskRightNeighborhood_iff
      ends m j k l zero p S (f x)).mpr
        ⟨x.1, (Finset.mem_erase.mp x.2).2, hf x⟩⟩
  have hginj : Function.Injective g := by
    intro x y hxy
    apply f.injective
    exact congrArg Subtype.val hxy
  have hcard : Fintype.card ↑(S.erase c) =
      Fintype.card
        ↑(canonicalMaskRightNeighborhood ends m j k l zero p S) := by
    simp only [Fintype.card_coe]
    rw [Finset.card_erase_of_mem hc]
    omega
  have hgbij : Function.Bijective g :=
    (Fintype.bijective_iff_injective_and_card g).mpr ⟨hginj, hcard⟩
  let e := Equiv.ofBijective g hgbij
  refine ⟨e, ?_⟩
  intro x
  change (g x).1 ∈ canonicalMaskRightImages
    ends m j k l zero p x.1
  exact hf x


theorem exists_canonicalMaskRightAugmentedEquiv
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (htight : (canonicalMaskRightNeighborhood
        ends m j k l zero p S).card + 1 = S.card)
    (hproper : ∀ T : Finset (leftMaskFiber ends m j k l zero p),
      T ⊂ S -> T.card ≤
        (canonicalMaskRightNeighborhood ends m j k l zero p T).card)
    (c : leftMaskFiber ends m j k l zero p) (hc : c ∈ S) :
    ∃ f : ↑S ≃ Option
        ↑(canonicalMaskRightNeighborhood ends m j k l zero p S),
      f ⟨c, hc⟩ = none ∧
        ∀ x : ↑S, x.1 ≠ c -> ∃ q,
          f x = some q ∧
            q.1 ∈ canonicalMaskRightImages
              ends m j k l zero p x.1 := by
  classical
  obtain ⟨e, he⟩ := exists_canonicalMaskRightNearPerfectEquiv
    ends m j k l zero p S htight hproper c hc
  have hset : (↑S : Set (leftMaskFiber ends m j k l zero p)) =
      ↑(insert c (S.erase c)) := by
    rw [Finset.insert_erase hc]
  let eDomain : ↑S ≃ ↑(insert c (S.erase c)) := Equiv.setCongr hset
  let eSplit : ↑(insert c (S.erase c)) ≃ Option ↑(S.erase c) :=
    Finset.subtypeInsertEquivOption (Finset.notMem_erase c S)
  let f := eDomain.trans (eSplit.trans (Equiv.optionCongr e))
  refine ⟨f, ?_, ?_⟩
  · have hval : ↑(eDomain ⟨c, hc⟩) = c := rfl
    simp [f, eSplit, Finset.subtypeInsertEquivOption, hval]
  · intro x hxc
    let xe : ↑(S.erase c) :=
      ⟨x.1, Finset.mem_erase.mpr ⟨hxc, x.2⟩⟩
    refine ⟨e xe, ?_, he xe⟩
    have hval : ↑(eDomain x) = x.1 := rfl
    simp [f, eSplit, Finset.subtypeInsertEquivOption, hval, xe]
    exact hxc


end StatMech.GrahamGHS.FourColor

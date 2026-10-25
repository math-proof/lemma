/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferComponentCut.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Def.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferMatching.Part9
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


@[simp] theorem mem_canonicalMaskRightAugmentedMatchingPairs_iff
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (c d : ↑S)
    (ef : canonicalMaskRightAugmentedEquivType
          ends m j k l zero p S ×
        canonicalMaskRightAugmentedEquivType ends m j k l zero p S) :
    ef ∈ canonicalMaskRightAugmentedMatchingPairs
        ends m j k l zero p S c d ↔
      CanonicalMaskRightAugmentedMatching
          ends m j k l zero p S c ef.1 ∧
        CanonicalMaskRightAugmentedMatching
          ends m j k l zero p S d ef.2 := by
  classical
  simp [canonicalMaskRightAugmentedMatchingPairs]

set_option maxHeartbeats 1000000 in


theorem canonicalMaskRightAugmentedMatchingPair_transition
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (c d : ↑S)
    (ef : canonicalMaskRightAugmentedEquivType
          ends m j k l zero p S ×
        canonicalMaskRightAugmentedEquivType ends m j k l zero p S)
    (hef : ef ∈ canonicalMaskRightAugmentedMatchingPairs
      ends m j k l zero p S c d) :
    let σ : Equiv.Perm ↑S := ef.1.trans ef.2.symm
    σ c = d ∧ ∀ x : ↑S, x ≠ c ->
      ∃ q : rightMaskFiber ends m j k l zero p,
        q ∈ canonicalMaskRightImages ends m j k l zero p x.1 ∧
          q ∈ canonicalMaskRightImages ends m j k l zero p (σ x).1 := by
  classical
  have hmatch := (mem_canonicalMaskRightAugmentedMatchingPairs_iff
    ends m j k l zero p S c d ef).mp hef
  rcases hmatch with ⟨⟨hfc0, hfc⟩, ⟨hfd0, hfd⟩⟩
  dsimp only
  constructor
  · apply ef.2.injective
    simp [hfc0, hfd0]
  · intro x hxc
    obtain ⟨q, hfcx, hqx⟩ := hfc x hxc
    have hfdσ : ef.2 (ef.1.trans ef.2.symm x) = some q := by
      rw [← hfcx]
      simp
    have hσd : ef.1.trans ef.2.symm x ≠ d := by
      intro hval
      rw [hval, hfd0] at hfdσ
      simp at hfdσ
    obtain ⟨r, hfdr, hr⟩ := hfd (ef.1.trans ef.2.symm x) hσd
    have hrq : r = q := by
      rw [hfdσ] at hfdr
      exact Option.some.inj hfdr.symm
    subst r
    exact ⟨q.1, hqx, hr⟩

set_option maxHeartbeats 1000000 in


theorem canonicalMaskRightAugmentedMatchingPair_secondCommon_displacement
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (c d : ↑S)
    (ef : canonicalMaskRightAugmentedEquivType
          ends m j k l zero p S ×
        canonicalMaskRightAugmentedEquivType ends m j k l zero p S)
    (hef : ef ∈ canonicalMaskRightAugmentedMatchingPairs
      ends m j k l zero p S c d)
    (x : ↑S) (hxc : x ≠ c) :
    let σ : Equiv.Perm ↑S := ef.1.trans ef.2.symm
    ∃ q : rightMaskFiber ends m j k l zero p,
      q ∈ canonicalMaskRightImages ends m j k l zero p x.1 ∧
      q ∈ canonicalMaskRightImages ends m j k l zero p (σ x).1 ∧
      ∀ r : rightMaskFiber ends m j k l zero p, r ≠ q ->
        r ∈ canonicalMaskRightImages ends m j k l zero p x.1 ->
        r ∈ canonicalMaskRightImages ends m j k l zero p (σ x).1 ->
        ∃ u v : ↑S,
          u ≠ c ∧ v ≠ d ∧ u ≠ x ∧ v ≠ σ x ∧ σ u = v ∧
            r ∈ canonicalMaskRightImages ends m j k l zero p u.1 ∧
            r ∈ canonicalMaskRightImages ends m j k l zero p v.1 := by
  classical
  have hmatch := (mem_canonicalMaskRightAugmentedMatchingPairs_iff
    ends m j k l zero p S c d ef).mp hef
  rcases hmatch with ⟨⟨hfc0, hfc⟩, ⟨hfd0, hfd⟩⟩
  dsimp only
  obtain ⟨q, hfcx, hqx⟩ := hfc x hxc
  have hfdσ : ef.2 (ef.1.trans ef.2.symm x) = some q := by
    rw [← hfcx]
    simp
  have hσd : ef.1.trans ef.2.symm x ≠ d := by
    intro hval
    rw [hval, hfd0] at hfdσ
    simp at hfdσ
  obtain ⟨q', hfdq', hqσ⟩ := hfd (ef.1.trans ef.2.symm x) hσd
  have hq'q : q' = q := by
    rw [hfdσ] at hfdq'
    exact Option.some.inj hfdq'.symm
  subst q'
  refine ⟨q.1, hqx, hqσ, ?_⟩
  intro r hrq hrx hrσ
  have hrS : r ∈ canonicalMaskRightNeighborhood
      ends m j k l zero p S :=
    (mem_canonicalMaskRightNeighborhood_iff
      ends m j k l zero p S r).mpr ⟨x.1, x.2, hrx⟩
  let rS : ↑(canonicalMaskRightNeighborhood
      ends m j k l zero p S) := ⟨r, hrS⟩
  let u : ↑S := ef.1.symm (some rS)
  let v : ↑S := ef.2.symm (some rS)
  have hfcu : ef.1 u = some rS := by simp [u]
  have hfdv : ef.2 v = some rS := by simp [v]
  have huc : u ≠ c := by
    intro h
    rw [h, hfc0] at hfcu
    simp at hfcu
  have hvd : v ≠ d := by
    intro h
    rw [h, hfd0] at hfdv
    simp at hfdv
  have hux : u ≠ x := by
    intro h
    have heq : some rS = some q := by
      rw [← hfcu, h, hfcx]
    have hrSq : rS = q := Option.some.inj heq
    exact hrq (congrArg Subtype.val hrSq)
  have hvσ : v ≠ ef.1.trans ef.2.symm x := by
    intro h
    have heq : some rS = some q := by
      rw [← hfdv, h, hfdσ]
    have hrSq : rS = q := Option.some.inj heq
    exact hrq (congrArg Subtype.val hrSq)
  have hσuv : ef.1.trans ef.2.symm u = v := by
    apply ef.2.injective
    rw [hfdv]
    simp [hfcu]
  obtain ⟨ru, hfcru, hru⟩ := hfc u huc
  have hruS : ru = rS := by
    rw [hfcu] at hfcru
    exact Option.some.inj hfcru.symm
  subst ru
  obtain ⟨rv, hfdrv, hrv⟩ := hfd v hvd
  have hrvS : rv = rS := by
    rw [hfdv] at hfdrv
    exact Option.some.inj hfdrv.symm
  subst rv
  exact ⟨u, v, huc, hvd, hux, hvσ, hσuv, hru, hrv⟩


theorem exists_canonicalMaskRightNeighbor_not_mem_of_properHall
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (hproper : ∀ T : Finset (leftMaskFiber ends m j k l zero p),
      T ⊂ S -> T.card ≤
        (canonicalMaskRightNeighborhood ends m j k l zero p T).card)
    (T : Finset (leftMaskFiber ends m j k l zero p)) (hTS : T ⊂ S)
    (R : Finset (rightMaskFiber ends m j k l zero p))
    (hcard : R.card < T.card) :
    ∃ x ∈ T, ∃ q : rightMaskFiber ends m j k l zero p,
      q ∈ canonicalMaskRightImages ends m j k l zero p x ∧ q ∉ R := by
  classical
  have hHall := hproper T hTS
  have hex : ∃ q ∈ canonicalMaskRightNeighborhood
      ends m j k l zero p T, q ∉ R := by
    by_contra h
    push Not at h
    have hsub : canonicalMaskRightNeighborhood
        ends m j k l zero p T ⊆ R := by
      intro q hq
      exact h q hq
    have hle := Finset.card_le_card hsub
    omega
  obtain ⟨q, hqT, hqR⟩ := hex
  obtain ⟨x, hxT, hqx⟩ := (mem_canonicalMaskRightNeighborhood_iff
    ends m j k l zero p T q).mp hqT
  exact ⟨x, hxT, q, hqx, hqR⟩


theorem exists_canonicalMaskRightNeighbor_ne_pair_of_properHall
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (hproper : ∀ T : Finset (leftMaskFiber ends m j k l zero p),
      T ⊂ S -> T.card ≤
        (canonicalMaskRightNeighborhood ends m j k l zero p T).card)
    (T : Finset (leftMaskFiber ends m j k l zero p)) (hTS : T ⊂ S)
    (hcard : 2 < T.card)
    (q r : rightMaskFiber ends m j k l zero p) :
    ∃ x ∈ T, ∃ s : rightMaskFiber ends m j k l zero p,
      s ∈ canonicalMaskRightImages ends m j k l zero p x ∧
        s ≠ q ∧ s ≠ r := by
  classical
  obtain ⟨x, hxT, s, hsx, hs⟩ :=
    exists_canonicalMaskRightNeighbor_not_mem_of_properHall
      ends m j k l zero p S hproper T hTS {q, r} (by
        have hp := Finset.card_insert_le q ({r} : Finset
          (rightMaskFiber ends m j k l zero p))
        simp only [Finset.card_singleton] at hp
        omega)
  refine ⟨x, hxT, s, hsx, ?_, ?_⟩
  · intro hsq
    exact hs (by simp [hsq])
  · intro hsr
    exact hs (by simp [hsr])


theorem canonicalMaskRightExposure_terminal_or_escapes
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (htight : (canonicalMaskRightNeighborhood
        ends m j k l zero p S).card + 1 = S.card)
    (hproper : ∀ T : Finset (leftMaskFiber ends m j k l zero p),
      T ⊂ S -> T.card ≤
        (canonicalMaskRightNeighborhood ends m j k l zero p T).card)
    (T : Finset (leftMaskFiber ends m j k l zero p)) (hTS : T ⊆ S)
    (R : Finset (rightMaskFiber ends m j k l zero p))
    (hR : R ⊆ canonicalMaskRightNeighborhood ends m j k l zero p T)
    (hdef : R.card + 1 = T.card) :
    (T = S ∧ R = canonicalMaskRightNeighborhood
        ends m j k l zero p S) ∨
      ∃ x ∈ T, ∃ q : rightMaskFiber ends m j k l zero p,
        q ∈ canonicalMaskRightImages ends m j k l zero p x ∧ q ∉ R := by
  classical
  by_cases hfull : T = S
  · left
    subst T
    refine ⟨rfl, Finset.eq_of_subset_of_card_le hR ?_⟩
    omega
  · right
    have hTS' : T ⊂ S :=
      (Finset.ssubset_iff_subset_ne).mpr ⟨hTS, hfull⟩
    exact exists_canonicalMaskRightNeighbor_not_mem_of_properHall
      ends m j k l zero p S hproper T hTS' R (by omega)


theorem exists_canonicalMaskRightAugmentedMatching_escape
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (hproper : ∀ T : Finset (leftMaskFiber ends m j k l zero p),
      T ⊂ S -> T.card ≤
        (canonicalMaskRightNeighborhood ends m j k l zero p T).card)
    (T : Finset (leftMaskFiber ends m j k l zero p)) (hTS : T ⊂ S)
    (c : ↑S)
    (f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S)
    (hf : CanonicalMaskRightAugmentedMatching
      ends m j k l zero p S c f)
    (R : Finset (rightMaskFiber ends m j k l zero p))
    (hcard : R.card < T.card)
    (hassigned : ∀ u : ↑S, u.1 ∈ T -> u ≠ c ->
      ∃ qS : ↑(canonicalMaskRightNeighborhood
          ends m j k l zero p S),
        f u = some qS ∧ qS.1 ∈ R) :
    ∃ x ∈ T,
      ∃ qS : ↑(canonicalMaskRightNeighborhood
          ends m j k l zero p S),
        qS.1 ∈ canonicalMaskRightImages ends m j k l zero p x ∧
        qS.1 ∉ R ∧
        ∃ u : ↑S,
          f u = some qS ∧ u.1 ∉ T ∧
          (S \ insert u.1 T).card < (S \ T).card := by
  classical
  obtain ⟨x, hxT, q, hqx, hqR⟩ :=
    exists_canonicalMaskRightNeighbor_not_mem_of_properHall
      ends m j k l zero p S hproper T hTS R hcard
  have hxS : x ∈ S := hTS.1 hxT
  have hqS : q ∈ canonicalMaskRightNeighborhood
      ends m j k l zero p S :=
    (mem_canonicalMaskRightNeighborhood_iff
      ends m j k l zero p S q).mpr ⟨x, hxS, hqx⟩
  let qS : ↑(canonicalMaskRightNeighborhood
      ends m j k l zero p S) := ⟨q, hqS⟩
  let u : ↑S := f.symm (some qS)
  have hfu : f u = some qS := by simp [u]
  have huc : u ≠ c := by
    intro h
    have hfc0 := hf.1
    rw [h, hfc0] at hfu
    simp at hfu
  have huT : u.1 ∉ T := by
    intro huT
    obtain ⟨rS, hfur, hrR⟩ := hassigned u huT huc
    have hrq : rS = qS := by
      apply Option.some.inj
      exact hfur.symm.trans hfu
    exact hqR (by simpa only [qS, hrq] using hrR)
  have huS : u.1 ∈ S := u.2
  have hsdiff : S \ insert u.1 T ⊂ S \ T := by
    rw [Finset.ssubset_iff_subset_ne]
    constructor
    · intro y hy
      exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hy).1,
        fun hyT => (Finset.mem_sdiff.mp hy).2 (Finset.mem_insert_of_mem hyT)⟩
    · intro heq
      have huOld : u.1 ∈ S \ T := Finset.mem_sdiff.mpr ⟨huS, huT⟩
      have huNew : u.1 ∈ S \ insert u.1 T := heq.symm ▸ huOld
      exact (Finset.mem_sdiff.mp huNew).2 (Finset.mem_insert_self _ _)
  exact ⟨x, hxT, qS, hqx, hqR, u, hfu, huT,
    Finset.card_lt_card hsdiff⟩


theorem exists_canonicalMaskRightAugmentedMatching_strictExposure
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (hproper : ∀ T : Finset (leftMaskFiber ends m j k l zero p),
      T ⊂ S -> T.card ≤
        (canonicalMaskRightNeighborhood ends m j k l zero p T).card)
    (T : Finset (leftMaskFiber ends m j k l zero p)) (hTS : T ⊂ S)
    (c : ↑S) (hcT : c.1 ∈ T)
    (f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S)
    (hf : CanonicalMaskRightAugmentedMatching
      ends m j k l zero p S c f) :
    ∃ x ∈ T,
      ∃ qS : ↑(canonicalMaskRightNeighborhood
          ends m j k l zero p S),
        qS.1 ∈ canonicalMaskRightImages ends m j k l zero p x ∧
        qS.1 ∉ canonicalMaskRightAugmentedAssignedRows
          ends m j k l zero p S T hTS.1 c f hf ∧
        ∃ u : ↑S,
          f u = some qS ∧ u.1 ∉ T ∧
          (S \ insert u.1 T).card < (S \ T).card := by
  classical
  let R := canonicalMaskRightAugmentedAssignedRows
    ends m j k l zero p S T hTS.1 c f hf
  have hRcard := card_canonicalMaskRightAugmentedAssignedRows
    ends m j k l zero p S T hTS.1 c hcT f hf
  have hcard : R.card < T.card := by
    dsimp only [R]
    omega
  have hassigned : ∀ u : ↑S, u.1 ∈ T -> u ≠ c ->
      ∃ qS : ↑(canonicalMaskRightNeighborhood
          ends m j k l zero p S),
        f u = some qS ∧ qS.1 ∈ R := by
    intro u huT huc
    simpa only [R] using canonicalMaskRightAugmentedAssignedRows_contains
      ends m j k l zero p S T hTS.1 c f hf u huT huc
  simpa only [R] using exists_canonicalMaskRightAugmentedMatching_escape
    ends m j k l zero p S hproper T hTS c f hf R hcard hassigned


theorem canonicalMaskRightAugmentedExposureClosed_eq_full
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (hproper : ∀ T : Finset (leftMaskFiber ends m j k l zero p),
      T ⊂ S -> T.card ≤
        (canonicalMaskRightNeighborhood ends m j k l zero p T).card)
    (c : ↑S)
    (f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S)
    (hf : CanonicalMaskRightAugmentedMatching
      ends m j k l zero p S c f)
    (T : Finset (leftMaskFiber ends m j k l zero p))
    (hTS : T ⊆ S) (hcT : c.1 ∈ T)
    (hclosed : ∀ x ∈ T, ∀ u : ↑S, ∀ huc : u ≠ c,
      (canonicalMaskRightAugmentedAssignedImage
          ends m j k l zero p S c f hf u huc).1 ∈
        canonicalMaskRightImages ends m j k l zero p x ->
      u.1 ∈ T) :
    T = S := by
  classical
  by_contra hne
  have hTS' : T ⊂ S :=
    (Finset.ssubset_iff_subset_ne).mpr ⟨hTS, hne⟩
  obtain ⟨x, hxT, qS, hqx, -, u, hfu, huT, -⟩ :=
    exists_canonicalMaskRightAugmentedMatching_strictExposure
      ends m j k l zero p S hproper T hTS' c hcT f hf
  have huc : u ≠ c := by
    intro h
    exact huT (h ▸ hcT)
  let qu := canonicalMaskRightAugmentedAssignedImage
    ends m j k l zero p S c f hf u huc
  have hqu := canonicalMaskRightAugmentedAssignedImage_apply
    ends m j k l zero p S c f hf u huc
  have hquq : qu = qS := by
    apply Option.some.inj
    exact hqu.symm.trans hfu
  apply huT
  apply hclosed x hxT u huc
  change qu.1 ∈ canonicalMaskRightImages ends m j k l zero p x
  rw [hquq]
  exact hqx


end StatMech.GrahamGHS.FourColor

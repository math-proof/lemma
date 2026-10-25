/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferComponentCut.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Def.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferMatching.Part10
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


set_option maxHeartbeats 1000000 in


theorem exists_minimal_canonicalMaskRightAugmentedMatchingPair
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (htight : (canonicalMaskRightNeighborhood
        ends m j k l zero p S).card + 1 = S.card)
    (hproper : ∀ T : Finset (leftMaskFiber ends m j k l zero p),
      T ⊂ S -> T.card ≤
        (canonicalMaskRightNeighborhood ends m j k l zero p T).card)
    (c d : ↑S) :
    ∃ ef ∈ canonicalMaskRightAugmentedMatchingPairs
        ends m j k l zero p S c d,
      ∀ gh ∈ canonicalMaskRightAugmentedMatchingPairs
          ends m j k l zero p S c d,
        canonicalPermMovedCard
            (ef.1.trans ef.2.symm : Equiv.Perm ↑S) ≤
          canonicalPermMovedCard
            (gh.1.trans gh.2.symm : Equiv.Perm ↑S) := by
  classical
  let P := canonicalMaskRightAugmentedMatchingPairs
    ends m j k l zero p S c d
  have hP : P.Nonempty := by
    obtain ⟨fc, hfc0, hfc⟩ := exists_canonicalMaskRightAugmentedEquiv
      ends m j k l zero p S htight hproper c.1 c.2
    obtain ⟨fd, hfd0, hfd⟩ := exists_canonicalMaskRightAugmentedEquiv
      ends m j k l zero p S htight hproper d.1 d.2
    refine ⟨(fc, fd), ?_⟩
    rw [mem_canonicalMaskRightAugmentedMatchingPairs_iff]
    constructor
    · refine ⟨hfc0, ?_⟩
      intro x hxc
      apply hfc x
      intro hval
      exact hxc (Subtype.ext hval)
    · refine ⟨hfd0, ?_⟩
      intro x hxd
      apply hfd x
      intro hval
      exact hxd (Subtype.ext hval)
  obtain ⟨ef, hefP, hefmin⟩ := P.exists_min_image
    (fun gh => canonicalPermMovedCard
      (gh.1.trans gh.2.symm : Equiv.Perm ↑S)) hP
  exact ⟨ef, hefP, hefmin⟩

set_option maxHeartbeats 1000000 in


theorem exists_minimal_canonicalMaskRightPair_with_displacement
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (htight : (canonicalMaskRightNeighborhood
        ends m j k l zero p S).card + 1 = S.card)
    (hproper : ∀ T : Finset (leftMaskFiber ends m j k l zero p),
      T ⊂ S -> T.card ≤
        (canonicalMaskRightNeighborhood ends m j k l zero p T).card)
    (c d : ↑S) :
    ∃ ef ∈ canonicalMaskRightAugmentedMatchingPairs
        ends m j k l zero p S c d,
      (∀ gh ∈ canonicalMaskRightAugmentedMatchingPairs
          ends m j k l zero p S c d,
        canonicalPermMovedCard
            (ef.1.trans ef.2.symm : Equiv.Perm ↑S) ≤
          canonicalPermMovedCard
            (gh.1.trans gh.2.symm : Equiv.Perm ↑S)) ∧
      CanonicalMaskRightSecondCommonDisplacement
        ends m j k l zero p S c d ef := by
  classical
  obtain ⟨ef, hef, hmin⟩ :=
    exists_minimal_canonicalMaskRightAugmentedMatchingPair
      ends m j k l zero p S htight hproper c d
  refine ⟨ef, hef, hmin, ?_⟩
  intro x hxc
  exact canonicalMaskRightAugmentedMatchingPair_secondCommon_displacement
    ends m j k l zero p S c d ef hef x hxc


theorem exists_canonicalMaskRightAlternatingPerm
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (htight : (canonicalMaskRightNeighborhood
        ends m j k l zero p S).card + 1 = S.card)
    (hproper : ∀ T : Finset (leftMaskFiber ends m j k l zero p),
      T ⊂ S -> T.card ≤
        (canonicalMaskRightNeighborhood ends m j k l zero p T).card)
    (c d : leftMaskFiber ends m j k l zero p)
    (hc : c ∈ S) (hd : d ∈ S) :
    ∃ σ : Equiv.Perm ↑S,
      σ ⟨c, hc⟩ = ⟨d, hd⟩ ∧
        ∀ x : ↑S, x.1 ≠ c ->
          ∃ q : rightMaskFiber ends m j k l zero p,
            q ∈ canonicalMaskRightImages ends m j k l zero p x.1 ∧
              q ∈ canonicalMaskRightImages
                ends m j k l zero p (σ x).1 := by
  classical
  obtain ⟨fc, hfc0, hfc⟩ := exists_canonicalMaskRightAugmentedEquiv
    ends m j k l zero p S htight hproper c hc
  obtain ⟨fd, hfd0, hfd⟩ := exists_canonicalMaskRightAugmentedEquiv
    ends m j k l zero p S htight hproper d hd
  let σ : Equiv.Perm ↑S := fc.trans fd.symm
  refine ⟨σ, ?_, ?_⟩
  · apply fd.injective
    simp [σ, hfc0, hfd0]
  · intro x hxc
    obtain ⟨q, hfcx, hqx⟩ := hfc x hxc
    have hfdσ : fd (σ x) = some q := by
      rw [← hfcx]
      simp [σ]
    have hσd : (σ x).1 ≠ d := by
      intro hval
      have hsub : σ x = ⟨d, hd⟩ := Subtype.ext hval
      rw [hsub, hfd0] at hfdσ
      simp at hfdσ
    obtain ⟨r, hfdr, hr⟩ := hfd (σ x) hσd
    have hrq : r = q := by
      rw [hfdσ] at hfdr
      exact Option.some.inj hfdr.symm
    subst r
    exact ⟨q.1, hqx, hr⟩


theorem exists_canonicalMaskTransferAdjacentPerm
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (htight : (canonicalMaskRightNeighborhood
        ends m j k l zero p S).card + 1 = S.card)
    (hproper : ∀ T : Finset (leftMaskFiber ends m j k l zero p),
      T ⊂ S -> T.card ≤
        (canonicalMaskRightNeighborhood ends m j k l zero p T).card)
    (c d : leftMaskFiber ends m j k l zero p)
    (hc : c ∈ S) (hd : d ∈ S)
    (hcd : CanonicalMaskTransferAdjacent ends m j k l zero p c d) :
    ∃ σ : Equiv.Perm ↑S,
      σ ⟨c, hc⟩ = ⟨d, hd⟩ ∧
        ∀ x : ↑S, CanonicalMaskTransferAdjacent
          ends m j k l zero p x.1 (σ x).1 := by
  classical
  obtain ⟨σ, hσcd, hσ⟩ := exists_canonicalMaskRightAlternatingPerm
    ends m j k l zero p S htight hproper c d hc hd
  refine ⟨σ, hσcd, ?_⟩
  intro x
  by_cases hxc : x.1 = c
  · have hx : x = ⟨c, hc⟩ := Subtype.ext hxc
    subst x
    simpa only [hσcd] using hcd
  · obtain ⟨q, hqx, hqσ⟩ := hσ x hxc
    exact (exists_mem_canonicalMaskRightImages_iff_adjacent
      ends m j k l zero p x.1 (σ x).1).mp ⟨q, hqx, hqσ⟩


theorem exists_canonicalTranslatedRowPerm
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (htight : (canonicalMaskRightNeighborhood
        ends m j k l zero p S).card + 1 = S.card)
    (hproper : ∀ T : Finset (leftMaskFiber ends m j k l zero p),
      T ⊂ S -> T.card ≤
        (canonicalMaskRightNeighborhood ends m j k l zero p T).card)
    (c d : leftMaskFiber ends m j k l zero p)
    (hc : c ∈ S) (hd : d ∈ S)
    (hcd : CanonicalMaskTransferAdjacent ends m j k l zero p c d) :
    ∃ σ : Equiv.Perm ↑S,
      σ ⟨c, hc⟩ = ⟨d, hd⟩ ∧
        ∀ x : ↑S, ∃ a b : leftMaskFiber ends m j k l zero p,
          RowSupportDisconnects ends m
              (canonicalTranslatedRow ends m k zero a.1.1 x.1.1.1) k zero ∧
            canonicalTranslatedRow ends m k zero a.1.1 x.1.1.1 =
              canonicalTranslatedRow ends m k zero b.1.1 (σ x).1.1.1 := by
  obtain ⟨σ, hσcd, hσ⟩ := exists_canonicalMaskTransferAdjacentPerm
    ends m j k l zero p S htight hproper c d hc hd hcd
  refine ⟨σ, hσcd, ?_⟩
  intro x
  exact (canonicalMaskTransferAdjacent_iff_exists_translatedRow
    hloop hjk hkl x.1 (σ x).1).mp (hσ x)


end StatMech.GrahamGHS.FourColor

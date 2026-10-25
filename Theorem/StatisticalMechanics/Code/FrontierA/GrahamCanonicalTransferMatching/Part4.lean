/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferComponentCut.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Def.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferMatching.Part4
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem card_le_canonicalMaskRightNeighborhood_of_reference
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (r : leftMaskFiber ends m j k l zero p)
    (hworks : ∀ c ∈ S,
      CanonicalTransferWorks ends m k zero r.1.1 c.1.1) :
    S.card ≤
      (canonicalMaskRightNeighborhood ends m j k l zero p S).card := by
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective
    (canonicalReferenceNeighborhoodEmbedding
      ends m j k l zero hloop hjk hkl p S r hworks)
    (canonicalReferenceNeighborhoodEmbedding
      ends m j k l zero hloop hjk hkl p S r hworks).injective


theorem canonicalMaskRightNeighborhood_union
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    [DecidableEq (rightMaskFiber ends m j k l zero p)]
    (S T : Finset (leftMaskFiber ends m j k l zero p)) :
    canonicalMaskRightNeighborhood ends m j k l zero p (S ∪ T) =
      canonicalMaskRightNeighborhood ends m j k l zero p S ∪
        canonicalMaskRightNeighborhood ends m j k l zero p T := by
  ext q
  rw [mem_canonicalMaskRightNeighborhood_iff, Finset.mem_union]
  constructor
  · rintro ⟨c, hc, hq⟩
    rw [Finset.mem_union] at hc
    rcases hc with hcS | hcT
    · exact Or.inl ((mem_canonicalMaskRightNeighborhood_iff
        ends m j k l zero p S q).mpr ⟨c, hcS, hq⟩)
    · exact Or.inr ((mem_canonicalMaskRightNeighborhood_iff
        ends m j k l zero p T q).mpr ⟨c, hcT, hq⟩)
  · rintro (hqS | hqT)
    · obtain ⟨c, hc, hq⟩ := (mem_canonicalMaskRightNeighborhood_iff
        ends m j k l zero p S q).mp hqS
      exact ⟨c, Finset.mem_union_left T hc, hq⟩
    · obtain ⟨c, hc, hq⟩ := (mem_canonicalMaskRightNeighborhood_iff
        ends m j k l zero p T q).mp hqT
      exact ⟨c, Finset.mem_union_right S hc, hq⟩


theorem canonicalMaskRightNeighborhood_disjoint_of_orbitSeparated
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S T : Finset (leftMaskFiber ends m j k l zero p))
    (hsep : ∀ c ∈ S, ∀ d ∈ T,
      ¬ CanonicalMaskTransferOrbit ends m j k l zero p c d) :
    Disjoint
      (canonicalMaskRightNeighborhood ends m j k l zero p S)
      (canonicalMaskRightNeighborhood ends m j k l zero p T) := by
  classical
  rw [Finset.disjoint_left]
  intro q hqS hqT
  obtain ⟨c, hcS, hqc⟩ := (mem_canonicalMaskRightNeighborhood_iff
    ends m j k l zero p S q).mp hqS
  obtain ⟨d, hdT, hqd⟩ := (mem_canonicalMaskRightNeighborhood_iff
    ends m j k l zero p T q).mp hqT
  apply hsep c hcS d hdT
  exact Relation.ReflTransGen.single
    ((exists_mem_canonicalMaskRightImages_iff_adjacent
      ends m j k l zero p c d).mp ⟨q, hqc, hqd⟩)


theorem card_le_canonicalMaskRightNeighborhood_union_of_orbitSeparated
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    [DecidableEq (rightMaskFiber ends m j k l zero p)]
    (S T : Finset (leftMaskFiber ends m j k l zero p))
    (hST : Disjoint S T)
    (hsep : ∀ c ∈ S, ∀ d ∈ T,
      ¬ CanonicalMaskTransferOrbit ends m j k l zero p c d)
    (hS : S.card ≤
      (canonicalMaskRightNeighborhood ends m j k l zero p S).card)
    (hT : T.card ≤
      (canonicalMaskRightNeighborhood ends m j k l zero p T).card) :
    (S ∪ T).card ≤
      (canonicalMaskRightNeighborhood ends m j k l zero p (S ∪ T)).card := by
  rw [canonicalMaskRightNeighborhood_union]
  rw [Finset.card_union_of_disjoint hST,
    Finset.card_union_of_disjoint
      (canonicalMaskRightNeighborhood_disjoint_of_orbitSeparated
        ends m j k l zero p S T hsep)]
  omega


theorem card_le_canonicalMaskRightNeighborhood_of_card_le_one
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (hcard : S.card ≤ 1) :
    S.card ≤
      (canonicalMaskRightNeighborhood ends m j k l zero p S).card := by
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨c, hc⟩ := hS
    apply card_le_canonicalMaskRightNeighborhood_of_reference
      ends m j k l zero hloop hjk hkl p S c
    intro d hd
    have hdc : d = c := (Finset.card_le_one.mp hcard) d hd c hc
    subst d
    exact canonicalTransferWorks_self hloop hjk hkl hk0 c
  · have hzero : S.card = 0 := Finset.card_eq_zero.mpr
      (Finset.not_nonempty_iff_eq_empty.mp hS)
    omega


end StatMech.GrahamGHS.FourColor

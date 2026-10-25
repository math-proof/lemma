import Mathlib
import sympy.Basic
import Theorem.Combinatorics.Enumerative.MinimalPermutationsEnumeration.Part14
open MetaMathlibExt


namespace MetaMathlibExt

/--
[ascent_of_mem_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MinimalPermutationsEnumeration.lean)
-/
@[path]
private lemma ascent_of_mem_singleton (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
  (a : Fin (d + 1))
  (ha : (Finset.univ.filter fun i : Fin (d + 1) =>
    σ i.castSucc < σ i.succ) = {a}) :
  σ a.castSucc < σ a.succ := by
  have hmem : a ∈ Finset.univ.filter (fun i : Fin (d + 1) =>
    σ i.castSucc < σ i.succ) := by
    rw [ha]
    exact Finset.mem_singleton_self a
  exact (Finset.mem_filter.mp hmem).2

end MetaMathlibExt

namespace MetaMathlibExt

/--
[topLarge_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MinimalPermutationsEnumeration.lean)
-/
@[path]
private lemma topLarge_card (d : ℕ) (a : Fin (d + 1)) :
  (topLarge d a).card = a.val + 2 := by
  simp only [topLarge, Fin.card_Ici]
  have ha := a.isLt
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[exclB_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MinimalPermutationsEnumeration.lean)
-/
@[path]
private lemma exclB_card (d : ℕ) (a : Fin (d + 1)) :
  (exclB d a).card = a.val + 2 := by
  have himg : exclB d a =
    Finset.image (fun M : Fin (d + 2) => (topLarge d a).erase M)
      (topLarge d a) := by
    ext L
    simp only [exclB, Finset.mem_filter, Finset.mem_powersetCard,
      Finset.mem_image]
    constructor
    · intro h
      obtain ⟨⟨hsub, hcard⟩, hsub2⟩ := h
      have hsdiff : (((topLarge d a) \ L).card) = 1 := by
        have h1 := topLarge_card d a
        have h2 := Finset.card_sdiff_of_subset hsub2
        omega
      obtain ⟨M, hM⟩ := Finset.card_eq_one.mp hsdiff
      have hmem : M ∈ topLarge d a ∧ M ∉ L := by
        have hmem' : M ∈ topLarge d a \ L := by
          rw [hM]
          exact Finset.mem_singleton_self M
        exact Finset.mem_sdiff.mp hmem'
      have heq : L = (topLarge d a).erase M := by
        ext x
        simp only [Finset.mem_erase]
        constructor
        · intro hx
          exact ⟨fun he => hmem.2 (he ▸ hx), hsub2 hx⟩
        · intro hx
          obtain ⟨hne, hx2⟩ := hx
          by_cases hx3 : x ∈ L
          · exact hx3
          · have hx4 : x ∈ topLarge d a \ L :=
            Finset.mem_sdiff.mpr ⟨hx2, hx3⟩
            rw [hM] at hx4
            have := Finset.mem_singleton.mp hx4
            exact absurd this hne
      exact ⟨M, hmem.1, heq.symm⟩
    · intro h
      obtain ⟨M, hM, rfl⟩ := h
      have hcard : ((topLarge d a).erase M).card = a.val + 1 := by
        rw [Finset.card_erase_of_mem hM, topLarge_card d a]
        omega
      have hsub : (topLarge d a).erase M ⊆ Finset.univ :=
        Finset.subset_univ _
      exact ⟨⟨hsub, hcard⟩, Finset.erase_subset _ _⟩
  rw [himg]
  have hinj : Set.InjOn (fun M : Fin (d + 2) => (topLarge d a).erase M)
    (topLarge d a) := by
    intro M1 hM1 M2 hM2 h
    have h' : (topLarge d a).erase M1 = (topLarge d a).erase M2 := h
    have hni : M1 ∉ (topLarge d a).erase M2 := by
      rw [← h']
      intro hm
      have := Finset.mem_erase.mp hm
      exact this.1 rfl
    have hmem1 : M1 ∈ topLarge d a := Finset.mem_coe.mp hM1
    have hne : ¬ M1 ≠ M2 := by
      intro hne2
      exact hni (Finset.mem_erase.mpr ⟨hne2, hmem1⟩)
    exact not_not.mp hne
  have hcard := Finset.card_image_of_injOn hinj
  rw [hcard, topLarge_card d a]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[topSmall_subset_topLarge](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MinimalPermutationsEnumeration.lean)
-/
@[path]
private lemma topSmall_subset_topLarge (d : ℕ) (a : Fin (d + 1))
  (hpos : 0 < a.val) : topSmall d a hpos ⊆ topLarge d a := by
  intro x hx
  simp only [topSmall, topLarge, Finset.mem_Ici] at hx ⊢
  have ha := a.isLt
  have hle : (⟨d - a.val, by omega⟩ : Fin (d + 2)) ≤
    (⟨d + 2 - a.val, by have ha := a.isLt; omega⟩ : Fin (d + 2)) := by
    simp only [Fin.le_def]
    omega
  exact le_trans hle hx

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mpeConstruct_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MinimalPermutationsEnumeration.lean)
-/
@[path]
private lemma mpeConstruct_apply (d : ℕ) (a : Fin (d + 1))
  (L : Finset (Fin (d + 2))) (hL : L.card = a.val + 1) (p : Fin (d + 2)) :
  mpeConstruct d a L hL p = mpeConstructFun d a L hL p :=
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mpePerms_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MinimalPermutationsEnumeration.lean)
-/
@[path]
private lemma mpePerms_mem (d : ℕ) (σ : Equiv.Perm (Fin (d + 2))) :
  σ ∈ mpePerms d ↔ mpeGood d σ := by
  classical
  simp only [mpePerms, Finset.mem_filter, Finset.mem_univ, true_and]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mpePositions_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MinimalPermutationsEnumeration.lean)
-/
@[path]
private lemma mpePositions_mem (d : ℕ) (a : Fin (d + 1)) :
  a ∈ mpePositions d ↔ 0 < a.val ∧ a.val < d := by
  simp only [mpePositions, Finset.mem_filter, Finset.mem_univ, true_and]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mpeAllowed_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MinimalPermutationsEnumeration.lean)
-/
@[path]
private lemma mpeAllowed_mem (d : ℕ) (a : Fin (d + 1)) (hpos : 0 < a.val)
  (L : Finset (Fin (d + 2))) :
  L ∈ mpeAllowed d a hpos ↔
    L.card = a.val + 1 ∧ L ∉ exclA d a hpos ∪ exclB d a := by
  simp only [mpeAllowed, Finset.mem_sdiff, Finset.mem_powersetCard,
    Finset.subset_univ, true_and]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mpeAllowedAt_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MinimalPermutationsEnumeration.lean)
-/
@[path]
private lemma mpeAllowedAt_eq (d : ℕ) (a : Fin (d + 1)) (hpos : 0 < a.val) :
  mpeAllowedAt d a = mpeAllowed d a hpos := by
  simp only [mpeAllowedAt, hpos, ↓reduceDIte]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mpe_excl_union_subset](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MinimalPermutationsEnumeration.lean)
-/
@[path]
private lemma mpe_excl_union_subset (d : ℕ) (a : Fin (d + 1))
  (hpos : 0 < a.val) :
  exclA d a hpos ∪ exclB d a ⊆
    Finset.powersetCard (a.val + 1) Finset.univ := by
  intro L hL
  obtain hA | hB := Finset.mem_union.mp hL
  · exact (Finset.mem_filter.mp hA).1
  · exact (Finset.mem_filter.mp hB).1

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mpePositions_eq_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MinimalPermutationsEnumeration.lean)
-/
@[path]
private lemma mpePositions_eq_Ioo (d : ℕ) :
  mpePositions d = Finset.Ioo (0 : Fin (d + 1)) (Fin.last d) := by
  ext a
  simp only [mpePositions_mem, Finset.mem_Ioo]
  change (0 < a.val ∧ a.val < d) ↔ 0 < a.val ∧ a.val < d
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mpePositions_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MinimalPermutationsEnumeration.lean)
-/
@[path]
private lemma mpePositions_card (d : ℕ) : (mpePositions d).card = d - 1 := by
  rw [mpePositions_eq_Ioo]
  simp only [Fin.card_Ioo, Fin.val_last, Fin.val_zero, Nat.sub_zero]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mpe_choose_sum_all](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MinimalPermutationsEnumeration.lean)
-/
@[path]
private lemma mpe_choose_sum_all (d : ℕ) :
  (∑ a : Fin (d + 1), Nat.choose (d + 2) (a.val + 1)) + 2 = 2 ^ (d + 2) := by
  have hsum := Nat.sum_range_choose (d + 2)
  rw [Finset.sum_range] at hsum
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc] at hsum
  simp only [Fin.val_zero, Fin.val_succ, Fin.val_castSucc, Fin.val_last,
    Nat.choose_zero_right, Nat.choose_self] at hsum
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mpe_univ_eq_insert_positions](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MinimalPermutationsEnumeration.lean)
-/
@[path]
private lemma mpe_univ_eq_insert_positions (d : ℕ) :
  (Finset.univ : Finset (Fin (d + 1))) =
    insert 0 (insert (Fin.last d) (mpePositions d)) := by
  ext a
  simp only [Finset.mem_univ, Finset.mem_insert, mpePositions_mem, true_iff]
  by_cases hzero : a.val = 0
  · exact Or.inl (Fin.ext hzero)
  · by_cases hlast : a.val = d
    · exact Or.inr (Or.inl (Fin.ext hlast))
    · exact Or.inr (Or.inr ⟨by omega, by have ha := a.isLt; omega⟩)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mpe_choose_sum_positions](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MinimalPermutationsEnumeration.lean)
-/
@[path]
private lemma mpe_choose_sum_positions (d : ℕ) (hd : 2 ≤ d) :
  (∑ a ∈ mpePositions d, Nat.choose (d + 2) (a.val + 1)) +
    2 * (d + 2) + 2 = 2 ^ (d + 2) := by
  have hzero : (0 : Fin (d + 1)) ∉ insert (Fin.last d) (mpePositions d) := by
    simp only [Finset.mem_insert, not_or]
    constructor
    · intro heq
      have hv := congrArg Fin.val heq
      simp only [Fin.val_zero, Fin.val_last] at hv
      omega
    · intro hmem
      have hbounds := (mpePositions_mem d 0).mp hmem
      simp only [Fin.val_zero] at hbounds
      omega
  have hlast : Fin.last d ∉ mpePositions d := by
    intro hmem
    have hbounds := (mpePositions_mem d (Fin.last d)).mp hmem
    simp only [Fin.val_last] at hbounds
    omega
  have hsum := mpe_choose_sum_all d
  change (∑ a ∈ (Finset.univ : Finset (Fin (d + 1))),
    Nat.choose (d + 2) (a.val + 1)) + 2 = 2 ^ (d + 2) at hsum
  rw [mpe_univ_eq_insert_positions d, Finset.sum_insert hzero,
    Finset.sum_insert hlast] at hsum
  simp only [Fin.val_zero, Fin.val_last, zero_add, Nat.choose_one_right,
    Nat.choose_succ_self_right] at hsum
  omega

end MetaMathlibExt

/--
[minimal_permutations_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MinimalPermutationsEnumeration.lean)
-/
@[path]
private lemma minimal_permutations_card_eq
  {d : ℕ} :
-- imply
  (Finset.univ.filter fun σ : Equiv.Perm (Fin (d + 2)) =>
    (Finset.univ.filter fun i : Fin (d + 1) =>
    σ i.castSucc > σ i.succ).card = d ∧
    ∀ j : Fin (d + 2),
    (Finset.univ.filter fun i : Fin d =>
    σ (j.succAbove i.castSucc) > σ (j.succAbove i.succ)).card < d).card =
    2 ^ (d + 2) - (d + 1) * (d + 2) - 2 := by
-- proof
  apply MetaMathlibExt.minimal_permutations_card d


-- created on 2026-10-20
-- updated on 2026-10-23

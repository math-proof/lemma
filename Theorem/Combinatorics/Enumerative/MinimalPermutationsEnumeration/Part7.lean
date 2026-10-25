/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MinimalPermutationsEnumeration.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Fin.Rev
import Mathlib.Order.Fin.Basic
import Def.Combinatorics.Enumerative.MinimalPermutationsEnumeration.Part6


section

namespace MetaMathlibExt

theorem mpeGood_forward (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (hgood : mpeGood d σ) :
    ∃ (a : Fin (d + 1)) (hpos : 0 < a.val), a.val < d ∧
      (Finset.univ.filter fun i : Fin (d + 1) =>
        σ i.castSucc < σ i.succ) = {a} ∧
      firstVals d σ a ∉ exclA d a hpos ∪ exclB d a := by
  obtain ⟨hdesc, hmin⟩ := hgood
  obtain ⟨a, ha⟩ := ascent_singleton_of_descent d σ hdesc
  have hpos : 0 < a.val := by
    by_contra h
    have hav : a.val = 0 := by omega
    have heq := end_first_not_minimal d σ a ha hav
    have hlt := hmin 0
    rw [heq] at hlt
    omega
  have hlt : a.val < d := by
    by_contra h
    have hav : a.val = d := by
      have hais := a.isLt
      omega
    have heq := end_last_not_minimal d σ a ha hav
    have hbad := hmin (Fin.last (d + 1))
    rw [heq] at hbad
    omega
  refine ⟨a, hpos, hlt, ha, ?_⟩
  simp only [Finset.mem_union, not_or]
  constructor
  · intro hA
    have hfail := left_failure_of_memA d σ a ha hpos hlt hA
    have hbridge := left_bridge_ascent_of_minimal d σ a ha hpos hmin
    exact lt_asymm hbridge hfail
  · intro hB
    have hfail := right_failure_of_memB d σ a ha hpos hlt hB
    have hbridge := right_bridge_ascent_of_minimal d σ a ha hlt hmin
    exact lt_asymm hbridge hfail

theorem mpeGood_backward (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (a : Fin (d + 1)) (hpos : 0 < a.val) (hlt : a.val < d)
    (ha : (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc < σ i.succ) = {a})
    (hallowed : firstVals d σ a ∉ exclA d a hpos ∪ exclB d a) :
    mpeGood d σ := by
  simp only [Finset.mem_union, not_or] at hallowed
  have hleft : σ (prevPos d a hpos) < σ a.succ := by
    have hposne : prevPos d a hpos ≠ a.succ := by
      intro heq
      have hv := congrArg Fin.val heq
      simp only [prevPos_val, Fin.val_succ] at hv
      omega
    have hne : σ (prevPos d a hpos) ≠ σ a.succ :=
      fun heq => hposne (σ.injective heq)
    rcases lt_or_gt_of_ne hne with hbridge | hfail
    · exact hbridge
    · exact absurd (mpe_mem_exclA_of_left_failure d σ a ha hpos hfail) hallowed.1
  have hright : σ a.castSucc < σ (nextPos d a hlt) := by
    have hposne : a.castSucc ≠ nextPos d a hlt := by
      intro heq
      have hv := congrArg Fin.val heq
      simp only [Fin.val_castSucc, nextPos_val] at hv
      omega
    have hne : σ a.castSucc ≠ σ (nextPos d a hlt) :=
      fun heq => hposne (σ.injective heq)
    rcases lt_or_gt_of_ne hne with hbridge | hfail
    · exact hbridge
    · exact absurd (mpe_mem_exclB_of_right_failure d σ a ha hlt hfail) hallowed.2
  have hasc : (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc < σ i.succ).card = 1 := by
    rw [ha]
    simp
  have hadd := descent_add_ascent d σ
  have hdesc : (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc > σ i.succ).card = d := by omega
  exact ⟨hdesc, minimal_of_bridges d σ a ha hpos hlt hleft hright⟩

theorem mpe_secondVals_eq_compl (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (a : Fin (d + 1)) :
    secondVals d σ a = (firstVals d σ a)ᶜ := by
  have hpartition := vals_disjoint_union d σ a
  ext x
  simp only [Finset.mem_compl]
  constructor
  · intro hxR hxL
    exact Finset.disjoint_left.mp hpartition.1 hxL hxR
  · intro hxL
    have hx : x ∈ firstVals d σ a ∪ secondVals d σ a := by
      rw [hpartition.2]
      exact Finset.mem_univ x
    rcases Finset.mem_union.mp hx with hx' | hx'
    · exact absurd hx' hxL
    · exact hx'

theorem mpe_block1_eq (d : ℕ) (σ τ : Equiv.Perm (Fin (d + 2)))
    (a : Fin (d + 1))
    (haσ : (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc < σ i.succ) = {a})
    (haτ : (Finset.univ.filter fun i : Fin (d + 1) =>
      τ i.castSucc < τ i.succ) = {a})
    (hvals : firstVals d σ a = firstVals d τ a) :
    (fun i : Fin (a.val + 1) => σ (block1Pos d a i)) =
      fun i => τ (block1Pos d a i) := by
  have hσ : (fun i : Fin (a.val + 1) =>
      σ (block1Pos d a (Fin.rev i))) =
      (firstVals d σ a).orderEmbOfFin (firstVals_card d σ a) := by
    apply Finset.orderEmbOfFin_unique
    · intro i
      simp only [firstVals, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨Fin.rev i, rfl⟩
    · exact (block1_anti d σ a haσ).comp Fin.rev_strictAnti
  have hτ : (fun i : Fin (a.val + 1) =>
      τ (block1Pos d a (Fin.rev i))) =
      (firstVals d σ a).orderEmbOfFin (firstVals_card d σ a) := by
    apply Finset.orderEmbOfFin_unique
    · intro i
      rw [hvals]
      simp only [firstVals, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨Fin.rev i, rfl⟩
    · exact (block1_anti d τ a haτ).comp Fin.rev_strictAnti
  funext i
  have hi := congrFun (hσ.trans hτ.symm) (Fin.rev i)
  simpa only [Fin.rev_rev] using hi

theorem mpe_block2_eq (d : ℕ) (σ τ : Equiv.Perm (Fin (d + 2)))
    (a : Fin (d + 1))
    (haσ : (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc < σ i.succ) = {a})
    (haτ : (Finset.univ.filter fun i : Fin (d + 1) =>
      τ i.castSucc < τ i.succ) = {a})
    (hvals : firstVals d σ a = firstVals d τ a) :
    (fun i : Fin ((d - a.val) + 1) => σ (block2Pos d a i)) =
      fun i => τ (block2Pos d a i) := by
  have hvals2 : secondVals d σ a = secondVals d τ a := by
    rw [mpe_secondVals_eq_compl d σ a, mpe_secondVals_eq_compl d τ a, hvals]
  have hσ : (fun i : Fin ((d - a.val) + 1) =>
      σ (block2Pos d a (Fin.rev i))) =
      (secondVals d σ a).orderEmbOfFin (secondVals_card d σ a) := by
    apply Finset.orderEmbOfFin_unique
    · intro i
      simp only [secondVals, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨Fin.rev i, rfl⟩
    · exact (block2_anti d σ a haσ).comp Fin.rev_strictAnti
  have hτ : (fun i : Fin ((d - a.val) + 1) =>
      τ (block2Pos d a (Fin.rev i))) =
      (secondVals d σ a).orderEmbOfFin (secondVals_card d σ a) := by
    apply Finset.orderEmbOfFin_unique
    · intro i
      rw [hvals2]
      simp only [secondVals, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨Fin.rev i, rfl⟩
    · exact (block2_anti d τ a haτ).comp Fin.rev_strictAnti
  funext i
  have hi := congrFun (hσ.trans hτ.symm) (Fin.rev i)
  simpa only [Fin.rev_rev] using hi

theorem mpe_reconstruct_injective (d : ℕ)
    (σ τ : Equiv.Perm (Fin (d + 2))) (a : Fin (d + 1))
    (haσ : (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc < σ i.succ) = {a})
    (haτ : (Finset.univ.filter fun i : Fin (d + 1) =>
      τ i.castSucc < τ i.succ) = {a})
    (hvals : firstVals d σ a = firstVals d τ a) : σ = τ := by
  have hblock1 := mpe_block1_eq d σ τ a haσ haτ hvals
  have hblock2 := mpe_block2_eq d σ τ a haσ haτ hvals
  apply Equiv.ext
  intro p
  by_cases hp : p.val ≤ a.val
  · let i : Fin (a.val + 1) := ⟨p.val, by omega⟩
    have heq : block1Pos d a i = p := by
      apply Fin.ext
      simp only [block1Pos_val]
      rfl
    rw [← heq]
    exact congrFun hblock1 i
  · have hle : a.val + 1 ≤ p.val := by omega
    let i : Fin ((d - a.val) + 1) :=
      ⟨p.val - (a.val + 1), by
        have hp' := p.isLt
        have ha' := a.isLt
        omega⟩
    have heq : block2Pos d a i = p := by
      apply Fin.ext
      simp only [block2Pos_val]
      change a.val + 1 + (p.val - (a.val + 1)) = p.val
      omega
    rw [← heq]
    exact congrFun hblock2 i

theorem mpe_compl_card (d : ℕ) (a : Fin (d + 1))
    (L : Finset (Fin (d + 2))) (hL : L.card = a.val + 1) :
    Lᶜ.card = (d - a.val) + 1 := by
  rw [Finset.card_compl, hL]
  simp only [Fintype.card_fin]
  have ha := a.isLt
  omega

end MetaMathlibExt
end

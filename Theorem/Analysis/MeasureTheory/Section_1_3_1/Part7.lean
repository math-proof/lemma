import Theorem.Analysis.MeasureTheory.Section_1_2_3.Part2
import Theorem.Analysis.Misc.NatBitwise
import Def.Analysis.MeasureTheory.Section_1_3_1.Part7


namespace UnsignedSimpleFunction.IntegralWellDef

open scoped Classical

/-- Single atoms are pairwise disjoint -/
lemma singleAtom_pairwiseDisjoint {X : Type*} {k : ℕ} (E : Fin k → Set X) :
    Set.univ.PairwiseDisjoint (singleAtom E) := by
  intro i _ j _ hij
  simp only [Function.onFun, singleAtom]
  have hlt_i : i.val < 2^(k+0) := by simp only [add_zero]; exact i.isLt
  have hlt_j : j.val < 2^(k+0) := by simp only [add_zero]; exact j.isLt
  have hij' : (⟨i.val, hlt_i⟩ : Fin (2^(k+0))) ≠ ⟨j.val, hlt_j⟩ := by
    intro h; apply hij; ext; exact Fin.mk.inj h
  exact atom_pairwiseDisjoint E (fun _ : Fin 0 => ∅) (by simp : i ∈ Set.univ) (by simp : j ∈ Set.univ) hij'

/-- Membership in singleAtom is determined by bit pattern -/
lemma mem_singleAtom_iff {X : Type*} {k : ℕ} (E : Fin k → Set X) (n : Fin (2^k)) (x : X) :
    x ∈ singleAtom E n ↔ ∀ i : Fin k, n.val.testBit i.val ↔ x ∈ E i := by
  simp only [singleAtom, atom, Set.mem_setOf_eq]
  constructor
  · intro ⟨h1, _⟩ i
    specialize h1 i
    rw [atomMembership_eq_testBit] at h1
    convert h1 using 1
  · intro h
    constructor
    · intro i
      rw [atomMembership_eq_testBit]
      exact h i
    · intro i; exact Fin.elim0 i

/-- Every point is in exactly one singleAtom -/
lemma exists_unique_singleAtom {X : Type*} [DecidableEq X] {k : ℕ} (E : Fin k → Set X) (x : X) :
    ∃! n : Fin (2^k), x ∈ singleAtom E n := by
  let n : ℕ := atomIndexOf E (fun _ : Fin 0 => ∅) x
  have hn_lt : n < 2^k := by
    have := atomIndexOf_lt E (fun _ : Fin 0 => ∅) x
    simp only [add_zero] at this
    exact this
  use ⟨n, hn_lt⟩
  constructor
  · simp only
    rw [mem_singleAtom_iff]
    intro i
    exact atomIndexOf_testBit_E E (fun _ : Fin 0 => ∅) x i
  · intro m hm
    ext
    rw [mem_singleAtom_iff] at hm
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < k
    · have h1 := hm ⟨j, hj⟩
      have h2 := atomIndexOf_testBit_E E (fun _ : Fin 0 => ∅) x ⟨j, hj⟩
      by_cases hx : x ∈ E ⟨j, hj⟩
      · rw [h1.mpr hx, h2.mpr hx]
      · have hm_false : (m.val.testBit j) = false := Bool.eq_false_iff.mpr (fun ht => hx (h1.mp ht))
        have hn_false : (n.testBit j) = false := Bool.eq_false_iff.mpr (fun ht => hx (h2.mp ht))
        rw [hm_false, hn_false]
    · have hm_lt : m.val < 2^k := m.isLt
      have hn_lt' : (atomIndexOf E (fun _ : Fin 0 => ∅) x) < 2^k := hn_lt
      rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hm_lt (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (le_of_not_gt hj)))]
      rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hn_lt' (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (le_of_not_gt hj)))]

end UnsignedSimpleFunction.IntegralWellDef

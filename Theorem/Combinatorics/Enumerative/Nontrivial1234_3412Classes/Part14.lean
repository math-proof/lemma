/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Data.Fintype.Perm
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Relation
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.SuccPred
import Mathlib.Order.Fin.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Def.Combinatorics.Enumerative.Nontrivial1234_3412Classes.Part14


namespace MetaMathlibExt

lemma ntDeletion_large {k : ℕ} (hk : 7 ≤ k)
    {σ : Equiv.Perm (Fin (k + 2))} (hσ : σ ∈ ntG (k + 1)) :
    ∃ y : Fin (k + 2), ∃ ρ ∈ ntG k, σ = ntIns y (σ y) ρ := by
  classical
  obtain ⟨o, htop, hbottom⟩ := ntChoose_occurrence (by omega) hσ.1 hσ.2.1
  let α₁ := σ * Equiv.swap o.a o.c
  let α₂ := σ * Equiv.swap o.b o.d
  have hac : o.a ≠ o.c := by
    intro h
    have hv := congrArg Fin.val h
    have hab := o.hab
    have hbc := o.hbc
    omega
  have hbd : o.b ≠ o.d := by
    intro h
    have hv := congrArg Fin.val h
    have hbc := o.hbc
    have hcd := o.hcd
    omega
  have hα₁ : ¬ntSemi α₁ := ntUnswap_not_semi hσ.2.1 hσ.2.2 hac
  have hα₂ : ¬ntSemi α₂ := ntUnswap_not_semi hσ.2.1 hσ.2.2 hbd
  have hD₁ : (ntDSemi α₁ \ o.positions).card ≤ 2 := by
    exact le_trans (Finset.card_le_card Finset.sdiff_subset)
      (ntDSemi_card_le_two (by omega) hα₁)
  have hD₂ : (ntDSemi α₂ \ o.positions).card ≤ 2 := by
    exact le_trans (Finset.card_le_card Finset.sdiff_subset)
      (ntDSemi_card_le_two (by omega) hα₂)
  have hDone : ntDSemi α₁ \ o.positions = ∅ ∨
      ntDSemi α₂ \ o.positions = ∅ := by
    exact ntDSemi_sdiff_not_both (by omega) o hα₂
  have hTbad : ((ntDSemi α₁ \ o.positions) ∪
      (ntDSemi α₂ \ o.positions)).card ≤ 2 := by
    rcases hDone with h | h
    · simp [h, hD₂]
    · simp [h, hD₁]
  have hEbad : (ntEBad σ \ o.positions).card ≤ 2 :=
    ntEBad_sdiff_card o htop hbottom
  let bad := (ntEBad σ \ o.positions) ∪
    ((ntDSemi α₁ \ o.positions) ∪ (ntDSemi α₂ \ o.positions))
  have hbad : bad.card ≤ 4 := by
    calc
      bad.card ≤ (ntEBad σ \ o.positions).card +
          ((ntDSemi α₁ \ o.positions) ∪
            (ntDSemi α₂ \ o.positions)).card := Finset.card_union_le _ _
      _ ≤ 4 := by omega
  let available := Finset.univ \ o.positions
  have hpositions : o.positions ⊆ (Finset.univ : Finset (Fin (k + 2))) :=
    fun _ _ => Finset.mem_univ _
  have havailable : available.card = k - 2 := by
    rw [Finset.card_sdiff_of_subset hpositions, Finset.card_univ,
      Fintype.card_fin, ntOccurrence_positions_card]
    omega
  have hnsub : ¬available ⊆ bad := by
    intro hsub
    have hcard := Finset.card_le_card hsub
    rw [havailable] at hcard
    omega
  obtain ⟨y, hyavailable, hybad⟩ := Finset.not_subset.mp hnsub
  have hypos : y ∉ o.positions := (Finset.mem_sdiff.mp hyavailable).2
  obtain ⟨ρ, hσρ⟩ := ntIns_exists y (σ y) σ rfl
  refine ⟨y, ρ, ?_, hσρ⟩
  refine ⟨?_, ntOccurrence_delete o hσρ hypos, ?_⟩
  · apply ntDeletion_memE_of_not_bad hσ.1 hσρ
    intro hyE
    apply hybad
    simp only [bad, Finset.mem_union]
    exact Or.inl (Finset.mem_sdiff.mpr ⟨hyE, hypos⟩)
  · intro j hj hK
    have hyD := ntK_delete_mem_DSemi o hσρ hypos hK
    apply hybad
    simp only [bad, Finset.mem_union]
    rcases Finset.mem_union.mp hyD with hyD | hyD
    · exact Or.inr (Or.inl (Finset.mem_sdiff.mpr ⟨hyD, hypos⟩))
    · exact Or.inr (Or.inr (Finset.mem_sdiff.mpr ⟨hyD, hypos⟩))

/-- Insertion step: non-inert insertions land in a reference class. -/
lemma ntInsertion {m : ℕ} (hm : 5 ≤ m)
    (hIH : ∀ ρ ∈ ntG (m + 1),
      Relation.EqvGen (ntMove (m + 2)) ρ (ntEven (m + 2)) ∨
        Relation.EqvGen (ntMove (m + 2)) ρ (ntOdd m))
    {y v : Fin (m + 3)} {ρ : Equiv.Perm (Fin (m + 2))}
    (hρ : ρ ∈ ntG (m + 1))
    (hyv : (y ≠ 0 ∨ v ≠ Fin.last (m + 2)) ∧
      (y ≠ Fin.last (m + 2) ∨ v ≠ 0)) :
    Relation.EqvGen (ntMove (m + 3)) (ntIns y v ρ) (ntEven (m + 3)) ∨
      Relation.EqvGen (ntMove (m + 3)) (ntIns y v ρ) (ntOdd (m + 1)) := by
  by_cases hp1 : (y.val, v.val) = (1, m + 2)
  · have hy : y = (⟨1, by omega⟩ : Fin (m + 3)) := by
      apply Fin.ext
      exact congrArg Prod.fst hp1
    have hv : v = (⟨m + 2, by omega⟩ : Fin (m + 3)) := by
      apply Fin.ext
      exact congrArg Prod.snd hp1
    rw [hy, hv]
    exact ntInsertion_pair1 hm hIH hρ
  by_cases hp2 : (y.val, v.val) = (m + 1, 0)
  · have hy : y = (⟨m + 1, by omega⟩ : Fin (m + 3)) := by
      apply Fin.ext
      exact congrArg Prod.fst hp2
    have hv : v = (⟨0, by omega⟩ : Fin (m + 3)) := by
      apply Fin.ext
      exact congrArg Prod.snd hp2
    rw [hy, hv]
    exact ntInsertion_pair2 hm hIH hρ
  by_cases hp3 : (y.val, v.val) = (m + 2, 1)
  · have hy : y = (⟨m + 2, by omega⟩ : Fin (m + 3)) := by
      apply Fin.ext
      exact congrArg Prod.fst hp3
    have hv : v = (⟨1, by omega⟩ : Fin (m + 3)) := by
      apply Fin.ext
      exact congrArg Prod.snd hp3
    rw [hy, hv]
    exact ntInsertion_pair3 hm hIH hρ
  by_cases hp4 : (y.val, v.val) = (0, m + 1)
  · have hy : y = (⟨0, by omega⟩ : Fin (m + 3)) := by
      apply Fin.ext
      exact congrArg Prod.fst hp4
    have hv : v = (⟨m + 1, by omega⟩ : Fin (m + 3)) := by
      apply Fin.ext
      exact congrArg Prod.snd hp4
    rw [hy, hv]
    exact ntInsertion_pair4 hm hIH hρ
  by_cases hb : 1 ≤ y.val ∧ 1 ≤ v.val
  · exact ntIns_branch1 hm hIH hρ hb.1 hb.2 hp1 hp3
  · have hc1 : y.val ≠ 0 ∨ v.val ≠ m + 2 := by
      rcases hyv.1 with hy | hv
      · exact Or.inl (fun h => hy (Fin.ext h))
      · exact Or.inr (fun h => hv (Fin.ext (by simpa using h)))
    have hc2 : y.val ≠ m + 2 ∨ v.val ≠ 0 := by
      rcases hyv.2 with hy | hv
      · exact Or.inl (fun h => hy (Fin.ext (by simpa using h)))
      · exact Or.inr (fun h => hv (Fin.ext h))
    have hb' : y.val < 1 ∨ v.val < 1 := by omega
    have hyU : y.val ≤ m + 1 := by
      rcases hb' with hy0 | hv0
      · omega
      · rcases hc2 with hyL | hvZ
        · omega
        · omega
    have hvU : v.val ≤ m + 1 := by
      rcases hb' with hy0 | hv0
      · rcases hc1 with hyZ | hvL
        · omega
        · omega
      · omega
    exact ntIns_branch2 hm hIH hρ hyU hvU hp4 hp2

end MetaMathlibExt

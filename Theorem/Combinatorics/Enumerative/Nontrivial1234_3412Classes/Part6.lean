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
import Def.Combinatorics.Enumerative.Nontrivial1234_3412Classes.Part6


namespace MetaMathlibExt

/-- The class count over the left-extreme set equals the count one size down. -/
lemma ntNcl_A {m : ℕ} :
    ntncl (ntMove (m + 2)) (ntA (m + 1)) = ntncl (ntMove (m + 1)) Set.univ := by
  have hf : Function.Injective (ntIns (0 : Fin (m + 2)) (Fin.last (m + 1))) :=
    ntIns_injective _ _
  have hiff : ∀ a b, ntMove (m + 1) a b ↔
      ntMove (m + 2) (ntIns (0 : Fin (m + 2)) (Fin.last (m + 1)) a)
        (ntIns (0 : Fin (m + 2)) (Fin.last (m + 1)) b) := by
    intro a b
    exact ⟨ntMove_ins _ _, ntMove_descent_zero_last (m := m + 1)⟩
  have hclosed : ∀ x ∈ Set.range (ntIns (0 : Fin (m + 2)) (Fin.last (m + 1))), ∀ y,
      (ntMove (m + 2) x y ∨ ntMove (m + 2) y x) →
        y ∈ Set.range (ntIns (0 : Fin (m + 2)) (Fin.last (m + 1))) := by
    intro x hx y hxy
    obtain ⟨ρ, rfl⟩ := hx
    have hx0 : (ntIns (0 : Fin (m + 2)) (Fin.last (m + 1)) ρ) 0 = Fin.last (m + 1) :=
      ntIns_apply_same _ _ _
    have hy0 : y 0 = Fin.last (m + 1) := ntMove_inert_zero hx0 hxy
    obtain ⟨ρ', rfl⟩ := ntIns_exists _ _ y hy0
    exact ⟨ρ', rfl⟩
  have hmap := ntNcl_map hf hiff hclosed Set.univ
  rw [ntRange_A] at hmap
  exact hmap

/-- The class count over the right-extreme set equals the count one size down. -/
lemma ntNcl_B {k : ℕ} :
    ntncl (ntMove (k + 1)) (ntB k) = ntncl (ntMove k) Set.univ := by
  have hf : Function.Injective (ntIns (Fin.last k) (0 : Fin (k + 1))) :=
    ntIns_injective _ _
  have hiff : ∀ a b, ntMove k a b ↔
      ntMove (k + 1) (ntIns (Fin.last k) (0 : Fin (k + 1)) a)
        (ntIns (Fin.last k) (0 : Fin (k + 1)) b) := by
    intro a b
    exact ⟨ntMove_ins _ _, ntMove_descent_last_zero (m := k)⟩
  have hclosed :
      ∀ x ∈ Set.range (ntIns (Fin.last k) (0 : Fin (k + 1))), ∀ y,
      (ntMove (k + 1) x y ∨ ntMove (k + 1) y x) →
        y ∈ Set.range (ntIns (Fin.last k) (0 : Fin (k + 1))) := by
    intro x hx y hxy
    obtain ⟨ρ, rfl⟩ := hx
    have hx0 : (ntIns (Fin.last k) (0 : Fin (k + 1)) ρ) (Fin.last k) = 0 :=
      ntIns_apply_same _ _ _
    have hy0 : y (Fin.last k) = 0 := ntMove_inert_last hx0 hxy
    obtain ⟨ρ', rfl⟩ := ntIns_exists _ _ y hy0
    exact ⟨ρ', rfl⟩
  have hmap := ntNcl_map hf hiff hclosed Set.univ
  rw [ntRange_B] at hmap
  exact hmap

/-- The two-step count recursion. -/
lemma ntCount_recursion (m : ℕ) :
    ntncl (ntMove (m + 2)) Set.univ + ntncl (ntMove m) Set.univ =
      2 * ntncl (ntMove (m + 1)) Set.univ + ntncl (ntMove (m + 2)) (ntE (m + 1)) := by
  have hAB : ∀ x ∈ ntA (m + 1) ∪ ntB (m + 1), ∀ y,
      (ntMove (m + 2) x y ∨ ntMove (m + 2) y x) → y ∈ ntA (m + 1) ∪ ntB (m + 1) := by
    intro x hx y hxy
    rcases hx with hx | hx
    · exact Or.inl (ntA_closed x hx y hxy)
    · exact Or.inr (ntB_closed x hx y hxy)
  have hdisj : Disjoint (ntE (m + 1)) (ntA (m + 1) ∪ ntB (m + 1)) := by
    rw [Set.disjoint_left]
    intro σ hE hn
    rcases hn with h | h
    · exact hE.1 h
    · exact hE.2 h
  have hunion : ntE (m + 1) ∪ (ntA (m + 1) ∪ ntB (m + 1)) = Set.univ := by
    ext σ
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    by_cases h0 : σ 0 = Fin.last (m + 1)
    · exact Or.inr (Or.inl h0)
    · by_cases hl : σ (Fin.last (m + 1)) = 0
      · exact Or.inr (Or.inr hl)
      · exact Or.inl ⟨h0, hl⟩
  have step1 := ntNcl_union hdisj (ntE_closed (m := m)) hAB
  rw [hunion] at step1
  have step2 := ntNcl_inter (ntA_closed (m := m)) (ntB_closed (m := m))
  have hI : ntncl (ntMove (m + 2)) (ntA (m + 1) ∩ ntB (m + 1)) =
      ntncl (ntMove m) Set.univ := by
    have hf : Function.Injective (ntIns (0 : Fin (m + 2)) (Fin.last (m + 1))) :=
      ntIns_injective _ _
    have hiff : ∀ a b, ntMove (m + 1) a b ↔
        ntMove (m + 2) (ntIns (0 : Fin (m + 2)) (Fin.last (m + 1)) a)
          (ntIns (0 : Fin (m + 2)) (Fin.last (m + 1)) b) := by
      intro a b
      exact ⟨ntMove_ins _ _, ntMove_descent_zero_last (m := m + 1)⟩
    have hclosed :
        ∀ x ∈ Set.range (ntIns (0 : Fin (m + 2)) (Fin.last (m + 1))), ∀ y,
        (ntMove (m + 2) x y ∨ ntMove (m + 2) y x) →
          y ∈ Set.range (ntIns (0 : Fin (m + 2)) (Fin.last (m + 1))) := by
      intro x hx y hxy
      obtain ⟨ρ, rfl⟩ := hx
      have hx0 : (ntIns (0 : Fin (m + 2)) (Fin.last (m + 1)) ρ) 0 =
          Fin.last (m + 1) := ntIns_apply_same _ _ _
      have hy0 : y 0 = Fin.last (m + 1) := ntMove_inert_zero hx0 hxy
      obtain ⟨ρ', rfl⟩ := ntIns_exists _ _ y hy0
      exact ⟨ρ', rfl⟩
    have hmap := ntNcl_map hf hiff hclosed (ntB m)
    have hBdown : ntncl (ntMove (m + 1)) (ntB m) = ntncl (ntMove m) Set.univ :=
      ntNcl_B (k := m)
    rw [ntInter_AB, hmap, hBdown]
  have hA := ntNcl_A (m := m)
  have hB : ntncl (ntMove (m + 2)) (ntB (m + 1)) =
      ntncl (ntMove (m + 1)) Set.univ := ntNcl_B (k := m + 1)
  omega

end MetaMathlibExt

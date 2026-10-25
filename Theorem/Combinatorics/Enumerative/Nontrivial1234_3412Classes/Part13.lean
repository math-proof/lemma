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
import Def.Combinatorics.Enumerative.Nontrivial1234_3412Classes.Part13


namespace MetaMathlibExt

lemma ntBoundary_subset_doubleSwap_breaks {n j : ℕ} (hj : j + 1 ≤ n)
    {a b c d : Fin n} (hab : a.val < b.val) (hbc : b.val < c.val)
    (hcd : c.val < d.val) :
    ntBoundary ({a, b, c, d} : Finset (Fin n)) ⊆
      ntBreaks (ntBeta n j hj * (Equiv.swap a c * Equiv.swap b d)) := by
  let _ : NeZero n := ⟨by omega⟩
  let P : Finset (Fin n) := {a, b, c, d}
  let δ := (Equiv.swap a c * Equiv.swap b d : Equiv.Perm (Fin n))
  have hsupp : δ.support = P := ntDoubleSwap_support hab hbc hcd
  have hmove (x : Fin n) : δ x ≠ x ↔ x ∈ P := by
    rw [← hsupp]
    simp only [Equiv.Perm.mem_support]
  intro i hi
  rw [nt_mem_breaks_beta_doubleSwap_iff hj]
  have hboundary := (nt_mem_boundary_iff P i).1 hi
  by_cases hiP : i ∈ P
  · have hriP : finRotate n i ∉ P := hboundary.mp hiP
    have hfix : δ (finRotate n i) = finRotate n i :=
      Equiv.Perm.notMem_support.mp (by rwa [hsupp])
    rw [hfix]
    intro heq
    have heq' := (finRotate n).injective heq
    exact (hmove i).2 hiP heq'.symm
  · have hriP : finRotate n i ∈ P := by
      by_contra h
      exact hiP (hboundary.mpr h)
    have hfix : δ i = i := Equiv.Perm.notMem_support.mp (by rwa [hsupp])
    rw [hfix]
    exact (hmove (finRotate n i)).2 hriP

lemma ntDoubleSwap_breaks_of_outside {n j : ℕ} (hj : j + 1 ≤ n)
    {a b c d i : Fin n} (hab : a.val < b.val) (hbc : b.val < c.val)
    (hcd : c.val < d.val)
    (hi : i ∉ ({a, b, c, d} : Finset (Fin n)))
    (hri : finRotate n i ∉ ({a, b, c, d} : Finset (Fin n))) :
    i ∉ ntBreaks (ntBeta n j hj * (Equiv.swap a c * Equiv.swap b d)) := by
  let _ : NeZero n := ⟨by omega⟩
  let P : Finset (Fin n) := {a, b, c, d}
  let δ := (Equiv.swap a c * Equiv.swap b d : Equiv.Perm (Fin n))
  have hsupp : δ.support = P := ntDoubleSwap_support hab hbc hcd
  have hfixi : δ i = i := Equiv.Perm.notMem_support.mp (by rwa [hsupp])
  have hfixri : δ (finRotate n i) = finRotate n i :=
    Equiv.Perm.notMem_support.mp (by rwa [hsupp])
  rw [nt_mem_breaks_beta_doubleSwap_iff hj, hfixi, hfixri]
  simp

lemma ntDoubleSwap_breaks_card_ge_three {n j : ℕ} (hn : 5 ≤ n)
    (hj : j + 1 ≤ n) {a b c d : Fin n}
    (hab : a.val < b.val) (hbc : b.val < c.val) (hcd : c.val < d.val) :
    3 ≤ (ntBreaks
      (ntBeta n j hj * (Equiv.swap a c * Equiv.swap b d))).card := by
  let _ : NeZero n := ⟨by omega⟩
  let P : Finset (Fin n) := {a, b, c, d}
  let γ := ntBeta n j hj * (Equiv.swap a c * Equiv.swap b d)
  have hab' : a ≠ b := by intro h; subst b; omega
  have hac : a ≠ c := by intro h; subst c; omega
  have had : a ≠ d := by intro h; subst d; omega
  have hbc' : b ≠ c := by intro h; subst c; omega
  have hbd : b ≠ d := by intro h; subst d; omega
  have hcd' : c ≠ d := by intro h; subst d; omega
  have hPcard : P.card = 4 := by
    simp [P, hab', hac, had, hbc', hbd, hcd']
  have hBne : (ntBoundary P).Nonempty := by
    apply ntBoundary_nonempty P (x₀ := a)
    · simp [P]
    · rw [hPcard]
      omega
  have hsub : ntBoundary P ⊆ ntBreaks γ :=
    ntBoundary_subset_doubleSwap_breaks hj hab hbc hcd
  have hnonzero : (ntBreaks γ).card ≠ 0 := by
    intro h
    have hempty := Finset.card_eq_zero.mp h
    obtain ⟨x, hx⟩ := hBne
    have := hsub hx
    rw [hempty] at this
    simp at this
  have hne1 : (ntBreaks γ).card ≠ 1 := nt_card_breaks_ne_one γ
  have hne2 : (ntBreaks γ).card ≠ 2 := nt_card_breaks_ne_two γ
  change 3 ≤ (ntBreaks γ).card
  omega

lemma ntDoubleSwap_three_shared_outside {n j : ℕ} (hn : 5 ≤ n)
    (hj : j + 1 ≤ n) {a b c d q : Fin n}
    (hab : a.val < b.val) (hbc : b.val < c.val) (hcd : c.val < d.val)
    (hcard : (ntBreaks
      (ntBeta n j hj * (Equiv.swap a c * Equiv.swap b d))).card = 3)
    (hq : q ∉ ({a, b, c, d} : Finset (Fin n)))
    (hprev : (finRotate n).symm q ∈ ntBreaks
      (ntBeta n j hj * (Equiv.swap a c * Equiv.swap b d)))
    (hnext : q ∈ ntBreaks
      (ntBeta n j hj * (Equiv.swap a c * Equiv.swap b d))) : n = 5 := by
  let _ : NeZero n := ⟨by omega⟩
  let P : Finset (Fin n) := {a, b, c, d}
  let γ := ntBeta n j hj * (Equiv.swap a c * Equiv.swap b d)
  let r := finRotate n
  let pred := r.symm q
  have hrpred : r pred = q := r.apply_symm_apply q
  have hrqP : r q ∈ P := by
    by_contra h
    exact (ntDoubleSwap_breaks_of_outside hj hab hbc hcd hq h) hnext
  have hpredP : pred ∈ P := by
    by_contra h
    apply (ntDoubleSwap_breaks_of_outside hj hab hbc hcd h ?_) hprev
    simpa only [pred, r, hrpred] using hq
  let B := ntBoundary P
  have hpredB : pred ∈ B := by
    apply (nt_mem_boundary_iff P pred).2
    rw [hrpred]
    exact ⟨fun _ => hq, fun _ => hpredP⟩
  have hqB : q ∈ B := by
    apply (nt_mem_boundary_iff P q).2
    exact ⟨fun h => False.elim (hq h), fun h => False.elim (h hrqP)⟩
  have hpredq : pred ≠ q := ntRotate_symm_ne_self (by omega) q
  have hpair : ({pred, q} : Finset (Fin n)) ⊆ B := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hpredB
    · exact hqB
  have hBsub : B ⊆ ntBreaks γ :=
    ntBoundary_subset_doubleSwap_breaks hj hab hbc hcd
  have hBle : B.card ≤ 3 := by
    calc
      B.card ≤ (ntBreaks γ).card := Finset.card_le_card hBsub
      _ = 3 := hcard
  have hBge : 2 ≤ B.card := by
    have h := Finset.card_le_card hpair
    simpa [hpredq] using h
  obtain ⟨t, ht⟩ := ntBoundary_card_even P
  change B.card = 2 * t at ht
  have hBcard : B.card = 2 := by omega
  have hpairCard : ({pred, q} : Finset (Fin n)).card = 2 := by simp [hpredq]
  have hBeq : B = {pred, q} := by
    exact (Finset.eq_of_subset_of_card_le hpair (by rw [hBcard, hpairCard])).symm
  let S := insert q P
  have hinv (i : Fin n) : i ∈ S ↔ r i ∈ S := by
    by_cases hiq : i = q
    · subst i
      simp [S, hrqP]
    by_cases hriq : r i = q
    · have hipred : i = pred := by
        apply r.injective
        rw [hriq, hrpred]
      have hiP : i ∈ P := by rwa [hipred]
      simp [S, hiq, hriq, hiP]
    · have hiB : i ∉ B := by
        rw [hBeq]
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        refine ⟨?_, hiq⟩
        intro hipred
        apply hriq
        rw [hipred, hrpred]
      have hiPiff : i ∈ P ↔ r i ∈ P := by
        by_cases hiP : i ∈ P
        · refine ⟨fun _ => ?_, fun _ => hiP⟩
          by_contra h
          apply hiB
          exact (nt_mem_boundary_iff P i).2 ⟨fun _ => h, fun _ => hiP⟩
        · refine ⟨fun h => False.elim (hiP h), fun hriP => ?_⟩
          exact False.elim (hiB ((nt_mem_boundary_iff P i).2
            ⟨fun h => False.elim (hiP h), fun h => False.elim (h hriP)⟩))
      simp only [S, Finset.mem_insert, hiq, hriq, false_or]
      exact hiPiff
  have hqS : q ∈ S := Finset.mem_insert_self q P
  have hiter : ∀ t : ℕ, (r^[t]) q ∈ S := by
    intro t
    induction t with
    | zero => simpa using hqS
    | succ t ih =>
        rw [Function.iterate_succ_apply']
        exact (hinv _).mp ih
  have hall : ∀ x : Fin n, x ∈ S := by
    intro x
    let z : Fin n := x - q
    have hx : (r^[z.val]) q = x := by
      rw [← finCycle_eq_finRotate_iterate (k := z)]
      simp [finCycle_apply, z]
    rw [← hx]
    exact hiter z.val
  have hSuniv : S = Finset.univ := Finset.eq_univ_of_forall hall
  have hPcard : P.card = 4 := by
    have hab' : a ≠ b := by intro h; subst b; omega
    have hac : a ≠ c := by intro h; subst c; omega
    have had : a ≠ d := by intro h; subst d; omega
    have hbc' : b ≠ c := by intro h; subst c; omega
    have hbd : b ≠ d := by intro h; subst d; omega
    have hcd' : c ≠ d := by intro h; subst d; omega
    simp [P, hab', hac, had, hbc', hbd, hcd']
  have hScard : S.card = 5 := by
    change (insert q P).card = 5
    rw [Finset.card_insert_of_notMem hq, hPcard]
  have huniv : S.card = n := by rw [hSuniv, Finset.card_univ, Fintype.card_fin]
  omega

lemma ntK_delete_mem_DSemi {m : ℕ} {σ : Equiv.Perm (Fin (m + 1))}
    (o : ntOccurrence σ) {y : Fin (m + 1)} {ρ : Equiv.Perm (Fin m)}
    (hσρ : σ = ntIns y (σ y) ρ) (hy : y ∉ o.positions)
    {j : ℕ} {hj : j + 1 ≤ m} (hK : ρ ∈ ntK m j hj) :
    y ∈ ntDSemi (σ * Equiv.swap o.a o.c) ∪
      ntDSemi (σ * Equiv.swap o.b o.d) := by
  obtain ⟨o', ha, hb, hc, hd⟩ := ntOccurrence_delete_data o hσρ hy
  obtain ⟨⟨P, Q, hPQ, hρ⟩, -⟩ := hK
  have hocc := ntBeta_occur hj hPQ hρ o'.hab o'.hbc o'.hcd o'.hpat
  rcases hocc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · apply Finset.mem_union.mpr
    left
    simpa only [ha, hc] using
      nt_mem_DSemi_unswap hj y (σ y) o'.a o'.c (hσρ.trans (congrArg (ntIns y (σ y)) hρ))
  · apply Finset.mem_union.mpr
    left
    rw [Equiv.swap_comm]
    simpa only [ha, hc] using
      nt_mem_DSemi_unswap hj y (σ y) o'.c o'.a (hσρ.trans (congrArg (ntIns y (σ y)) hρ))
  · apply Finset.mem_union.mpr
    right
    simpa only [hb, hd] using
      nt_mem_DSemi_unswap hj y (σ y) o'.b o'.d (hσρ.trans (congrArg (ntIns y (σ y)) hρ))
  · apply Finset.mem_union.mpr
    right
    rw [Equiv.swap_comm]
    simpa only [hb, hd] using
      nt_mem_DSemi_unswap hj y (σ y) o'.d o'.b (hσρ.trans (congrArg (ntIns y (σ y)) hρ))

lemma ntDSemi_sdiff_not_both {k : ℕ} (hk : 6 ≤ k)
    {σ : Equiv.Perm (Fin (k + 2))} (o : ntOccurrence σ)
    (hα₂ : ¬ntSemi (σ * Equiv.swap o.b o.d)) :
    ntDSemi (σ * Equiv.swap o.a o.c) \ o.positions = ∅ ∨
      ntDSemi (σ * Equiv.swap o.b o.d) \ o.positions = ∅ := by
  classical
  by_contra hboth
  simp only [not_or] at hboth
  have hD₁ne : (ntDSemi (σ * Equiv.swap o.a o.c) \ o.positions).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hboth.1
  have hD₂ne : (ntDSemi (σ * Equiv.swap o.b o.d) \ o.positions).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hboth.2
  obtain ⟨y₁, hy₁mem⟩ := hD₁ne
  have hy₁ := Finset.mem_sdiff.mp hy₁mem
  have hy₁D := hy₁.1
  have hy₁P := hy₁.2
  obtain ⟨y₂, hy₂mem⟩ := hD₂ne
  have hy₂ := Finset.mem_sdiff.mp hy₂mem
  have hy₂D := hy₂.1
  have hy₂P := hy₂.2
  obtain ⟨ρσ, hσρ⟩ := ntIns_exists y₁ (σ y₁) σ rfl
  obtain ⟨o', ha, hb, hc, hd⟩ := ntOccurrence_delete_data o hσρ hy₁P
  obtain ⟨β, hα₁ins, hβsemi⟩ :=
    (nt_mem_DSemi_iff (σ * Equiv.swap o.a o.c) y₁).1 hy₁D
  obtain ⟨j, hj, hβ⟩ := hβsemi
  let γ := ntBeta (k + 1) j hj *
    (Equiv.swap o'.a o'.c * Equiv.swap o'.b o'.d)
  have hrel : σ * Equiv.swap o.b o.d =
      (σ * Equiv.swap o.a o.c) * Equiv.swap o.a o.c * Equiv.swap o.b o.d := by
    rw [mul_assoc σ (Equiv.swap o.a o.c) (Equiv.swap o.a o.c),
      Equiv.swap_mul_self, mul_one]
  have hAC : ntIns y₁ ((σ * Equiv.swap o.a o.c) y₁) β * Equiv.swap o.a o.c =
      ntIns y₁ ((σ * Equiv.swap o.a o.c) y₁) (β * Equiv.swap o'.a o'.c) := by
    rw [← ha, ← hc, ← ntIns_mul_swap]
  have hBD : ntIns y₁ ((σ * Equiv.swap o.a o.c) y₁)
      (β * Equiv.swap o'.a o'.c) * Equiv.swap o.b o.d =
      ntIns y₁ ((σ * Equiv.swap o.a o.c) y₁)
        ((β * Equiv.swap o'.a o'.c) * Equiv.swap o'.b o'.d) := by
    rw [← hb, ← hd, ← ntIns_mul_swap]
  have hα₂ins : σ * Equiv.swap o.b o.d =
      ntIns y₁ ((σ * Equiv.swap o.a o.c) y₁) γ := by
    calc
      σ * Equiv.swap o.b o.d =
          (σ * Equiv.swap o.a o.c) * Equiv.swap o.a o.c * Equiv.swap o.b o.d := hrel
      _ = ntIns y₁ ((σ * Equiv.swap o.a o.c) y₁) β *
          Equiv.swap o.a o.c * Equiv.swap o.b o.d :=
        congrArg (fun τ => τ * Equiv.swap o.a o.c * Equiv.swap o.b o.d) hα₁ins
      _ = ntIns y₁ ((σ * Equiv.swap o.a o.c) y₁)
          (β * Equiv.swap o'.a o'.c) * Equiv.swap o.b o.d := by
        rw [hAC]
      _ = ntIns y₁ ((σ * Equiv.swap o.a o.c) y₁)
          ((β * Equiv.swap o'.a o'.c) * Equiv.swap o'.b o'.d) := by
        exact hBD
      _ = ntIns y₁ ((σ * Equiv.swap o.a o.c) y₁) γ := by
        rw [hβ]
        rfl
  have hα₂card : (ntBreaks (σ * Equiv.swap o.b o.d)).card = 3 :=
    ntBreaks_card_eq_three_of_mem_DSemi (by omega) hα₂ hy₂D
  have hγle : (ntBreaks γ).card ≤ 3 := by
    have h := ntBreaks_delete_card_le (by omega) y₁
      ((σ * Equiv.swap o.a o.c) y₁) γ
    rw [← hα₂ins, hα₂card] at h
    exact h
  have hγge : 3 ≤ (ntBreaks γ).card := by
    change 3 ≤ (ntBreaks (ntBeta (k + 1) j hj *
      (Equiv.swap o'.a o'.c * Equiv.swap o'.b o'.d))).card
    exact ntDoubleSwap_breaks_card_ge_three (by omega) hj o'.hab o'.hbc o'.hcd
  have hγcard : (ntBreaks γ).card = 3 := by omega
  let f := ntBreakMap y₁ ((σ * Equiv.swap o.a o.c) y₁) γ
  let I := (ntBreaks γ).image f
  have hImaps : I ⊆ ntBreaks (σ * Equiv.swap o.b o.d) := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    change ntBreakMap y₁ ((σ * Equiv.swap o.a o.c) y₁) γ z ∈ _
    rw [hα₂ins]
    exact ntBreakMap_mem (by omega) y₁ ((σ * Equiv.swap o.a o.c) y₁) γ hz
  have hfinj : (ntBreaks γ : Set (Fin (k + 1))).InjOn f :=
    ntBreakMap_injOn y₁ ((σ * Equiv.swap o.a o.c) y₁) γ
  have hIcard : I.card = 3 := by
    change ((ntBreaks γ).image f).card = 3
    rw [Finset.card_image_of_injOn hfinj, hγcard]
  have hIeq : I = ntBreaks (σ * Equiv.swap o.b o.d) :=
    Finset.eq_of_subset_of_card_le hImaps (by rw [hα₂card, hIcard])
  have hpre {x : Fin (k + 2)} (hx : x ∈ ntBreaks (σ * Equiv.swap o.b o.d)) :
      ∃ z ∈ ntBreaks γ, f z = x := by
    have hxI : x ∈ I := by rw [hIeq]; exact hx
    exact Finset.mem_image.mp hxI
  have hy₂pair := ntDSemi_pair_mem (by omega) hα₂ hy₂D
  let pred₂ := (finRotate (k + 2)).symm y₂
  have hpred₂ : pred₂ ∈ ntBreaks (σ * Equiv.swap o.b o.d) := hy₂pair.1
  have hy₂break : y₂ ∈ ntBreaks (σ * Equiv.swap o.b o.d) := hy₂pair.2
  by_cases hy₁₂ : y₁ = y₂
  · subst y₂
    obtain ⟨z, hz, hfz⟩ := hpre hy₂break
    change ntBreakMap y₁ ((σ * Equiv.swap o.a o.c) y₁) γ z = y₁ at hfz
    have hcross : finRotate (k + 2) (y₁.succAbove z) = y₁ := by
      exact ntBreakMap_cross_of_eq y₁ ((σ * Equiv.swap o.a o.c) y₁) γ z hfz
    have hw : y₁.succAbove z = pred₂ := by
      apply (finRotate (k + 2)).injective
      rw [hcross, (finRotate (k + 2)).apply_symm_apply]
    have hpredIns : pred₂ ∈
        ntBreaks (ntIns y₁ ((σ * Equiv.swap o.a o.c) y₁) γ) := by
      rw [← hα₂ins]
      exact hpred₂
    have hfprev : f z = pred₂ := by
      unfold f ntBreakMap
      dsimp only
      rw [ite_eq_left hcross, ite_eq_left (by simpa only [hw] using hpredIns), hw]
    have hne : pred₂ ≠ y₁ := by
      change (finRotate (k + 2)).symm y₁ ≠ y₁
      exact ntRotate_symm_ne_self (by omega) y₁
    exact hne (hfprev.symm.trans hfz)
  · obtain ⟨q, hq⟩ := Fin.exists_succAbove_eq (Ne.symm hy₁₂)
    have hqP : q ∉ o'.positions := by
      intro h
      simp only [ntOccurrence.positions, Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl | rfl | rfl
      · apply hy₂P
        rw [← hq, ha]
        simp [ntOccurrence.positions]
      · apply hy₂P
        rw [← hq, hb]
        simp [ntOccurrence.positions]
      · apply hy₂P
        rw [← hq, hc]
        simp [ntOccurrence.positions]
      · apply hy₂P
        rw [← hq, hd]
        simp [ntOccurrence.positions]
    obtain ⟨z₂, hz₂, hfz₂⟩ := hpre hy₂break
    change ntBreakMap y₁ ((σ * Equiv.swap o.a o.c) y₁) γ z₂ = y₂ at hfz₂
    have hfz₂not : ntBreakMap y₁ ((σ * Equiv.swap o.a o.c) y₁) γ z₂ ≠ y₁ := by
      rw [hfz₂]
      exact Ne.symm hy₁₂
    have hwz₂ : y₁.succAbove z₂ = y₂ := by
      have h := ntBreakMap_eq_succAbove_of_ne y₁
        ((σ * Equiv.swap o.a o.c) y₁) γ z₂ hfz₂not
      rw [hfz₂] at h
      exact h.symm
    have hz₂q : z₂ = q := Fin.succAbove_right_injective (hwz₂.trans hq.symm)
    have hqbreak : q ∈ ntBreaks γ := by rwa [← hz₂q]
    obtain ⟨z₁, hz₁, hfz₁⟩ := hpre hpred₂
    change ntBreakMap y₁ ((σ * Equiv.swap o.a o.c) y₁) γ z₁ = pred₂ at hfz₁
    have hrot : finRotate (k + 1) z₁ = q := by
      by_cases hp : pred₂ = y₁
      · have hcross : finRotate (k + 2) (y₁.succAbove z₁) = y₁ := by
          apply ntBreakMap_cross_of_eq y₁ ((σ * Equiv.swap o.a o.c) y₁) γ z₁
          rw [hfz₁, hp]
        have hpos := ntRotate_succAbove_cross (by omega) y₁ z₁ hcross
        apply Fin.succAbove_right_injective
        rw [hpos, hq]
        change finRotate (k + 2) y₁ = y₂
        rw [← hp]
        exact (finRotate (k + 2)).apply_symm_apply y₂
      · have hfz₁not : ntBreakMap y₁ ((σ * Equiv.swap o.a o.c) y₁) γ z₁ ≠ y₁ := by
          rw [hfz₁]
          exact hp
        have hwz₁ : y₁.succAbove z₁ = pred₂ := by
          have h := ntBreakMap_eq_succAbove_of_ne y₁
            ((σ * Equiv.swap o.a o.c) y₁) γ z₁ hfz₁not
          rw [hfz₁] at h
          exact h.symm
        have hcross : finRotate (k + 2) (y₁.succAbove z₁) ≠ y₁ := by
          rw [hwz₁, (finRotate (k + 2)).apply_symm_apply]
          exact Ne.symm hy₁₂
        have hpos := ntRotate_succAbove (by omega) y₁ z₁ hcross
        apply Fin.succAbove_right_injective
        rw [← hpos, hwz₁, (finRotate (k + 2)).apply_symm_apply, hq]
    have hz₁prev : z₁ = (finRotate (k + 1)).symm q := by
      apply (finRotate (k + 1)).injective
      rw [hrot, (finRotate (k + 1)).apply_symm_apply]
    have hfive : k + 1 = 5 := by
      apply ntDoubleSwap_three_shared_outside (by omega) hj o'.hab o'.hbc o'.hcd
      · exact hγcard
      · exact hqP
      · rwa [← hz₁prev]
      · exact hqbreak
    omega

end MetaMathlibExt

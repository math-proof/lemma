/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternStirlingRecursion.lean -/

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.MeshPatternStirlingRecursion.Part4


section

namespace MetaMathlibExt

/-- `MatchPred` transfers across the insertion at shifted positions. -/
lemma Phi_match_transfer (t a : ℕ) (p : Fin ((t.succ).succ))
    (τ : Equiv.Perm (Fin (t.succ))) (j : Fin (t.succ)) :
    MatchPred (a + 2) (Phi (t.succ) p τ) (p.succAbove j) ↔
      MatchPred (a + 2) τ j := by
  have hM' := maxPos_max t τ
  have hMσ := Phi_max (t.succ) p τ (maxPos t τ) hM'
  rw [match_of_max _ _ _ _ hMσ, match_of_max _ _ _ _ hM']
  rw [Phi_ltr_succAbove]
  have hcard := Phi_filter_card (t.succ) p τ (maxPos t τ) j
  constructor
  · rintro ⟨hl, hc⟩
    exact ⟨hl, by rwa [← hcard] at hc⟩
  · rintro ⟨hl, hc⟩
    exact ⟨hl, by rwa [hcard] at hc⟩

/-- `MatchPred` at the insertion point holds iff it is at the front with large max. -/
lemma Phi_match_p (t a : ℕ) (p : Fin ((t.succ).succ))
    (τ : Equiv.Perm (Fin (t.succ))) :
    MatchPred (a + 2) (Phi (t.succ) p τ) p ↔
      (p = 0 ∧ a + 1 ≤ (maxPos t τ).val) := by
  have hM' := maxPos_max t τ
  have hMσ := Phi_max (t.succ) p τ (maxPos t τ) hM'
  have hsub : a + 2 - 1 = a + 1 := by omega
  rw [match_of_max _ _ _ _ hMσ p, Phi_ltr_p]
  constructor
  · rintro ⟨hl, hc⟩
    subst hl
    refine ⟨rfl, ?_⟩
    have h0 := Phi_filter_p0 (t.succ) τ (maxPos t τ)
    omega
  · rintro ⟨rfl, hu⟩
    refine ⟨rfl, ?_⟩
    have h0 := Phi_filter_p0 (t.succ) τ (maxPos t τ)
    omega

/-- The match set of `σ = Phi p τ` is the shifted match set of `τ` plus possibly `p`. -/
lemma Phi_filter_set (t a : ℕ) (p : Fin ((t.succ).succ))
    (τ : Equiv.Perm (Fin (t.succ))) :
    Finset.univ.filter (MatchPred (a + 2) (Phi (t.succ) p τ))
      = (Finset.univ.filter (MatchPred (a + 2) τ)).map
          ⟨p.succAbove, Fin.succAbove_right_injective⟩ ∪
        (if p = 0 ∧ a + 1 ≤ (maxPos t τ).val then {p} else ∅) := by
  ext x
  by_cases hxp : x = p
  · subst hxp
    have hL : (x ∈ Finset.univ.filter (MatchPred (a + 2) (Phi (t.succ) x τ)))
        ↔ (x = 0 ∧ a + 1 ≤ (maxPos t τ).val) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Phi_match_p t a x τ
    have hR : (x ∈ (Finset.univ.filter (MatchPred (a + 2) τ)).map
          ⟨x.succAbove, Fin.succAbove_right_injective⟩ ∪
        (if x = 0 ∧ a + 1 ≤ (maxPos t τ).val then ({x} : Finset _) else ∅))
        ↔ (x = 0 ∧ a + 1 ≤ (maxPos t τ).val) := by
      have hne : ¬ ∃ j : Fin (t.succ),
          j ∈ Finset.univ.filter (MatchPred (a + 2) τ) ∧ x.succAbove j = x := by
        rintro ⟨j, _, hj⟩
        exact Fin.succAbove_ne x j hj
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk,
        Finset.mem_union, hne, false_or]
      by_cases hcond : x = 0 ∧ a + 1 ≤ (maxPos t τ).val
      · rw [ite_eq_left hcond]
        exact iff_of_true (Finset.mem_singleton_self x) hcond
      · rw [ite_eq_right hcond]
        exact iff_of_false (Finset.notMem_empty x) hcond
    rw [hL, hR]
  · have hnot : x ∉ (if p = 0 ∧ a + 1 ≤ (maxPos t τ).val then
        ({p} : Finset (Fin ((t.succ).succ))) else ∅) := by
      by_cases hcond : p = 0 ∧ a + 1 ≤ (maxPos t τ).val
      · rw [ite_eq_left hcond]
        simp [hxp]
      · rw [ite_eq_right hcond]
        simp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Finset.mem_union, hnot, or_false]
    constructor
    · intro hx
      obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hxp
      exact ⟨j, (Phi_match_transfer t a p τ j).mp hx, rfl⟩
    · rintro ⟨j, hjmem, hjx⟩
      subst hjx
      exact (Phi_match_transfer t a p τ j).mpr hjmem

/-- Cardinality version of the match-set identity. -/
lemma Phi_filter_card_eq (t a : ℕ) (p : Fin ((t.succ).succ))
    (τ : Equiv.Perm (Fin (t.succ))) :
    (Finset.univ.filter (MatchPred (a + 2) (Phi (t.succ) p τ))).card
      = (Finset.univ.filter (MatchPred (a + 2) τ)).card
        + (if p = 0 ∧ a + 1 ≤ (maxPos t τ).val then 1 else 0) := by
  have hdisj : Disjoint
      ((Finset.univ.filter (MatchPred (a + 2) τ)).map
        ⟨p.succAbove, Fin.succAbove_right_injective⟩)
      (if p = 0 ∧ a + 1 ≤ (maxPos t τ).val then ({p} : Finset _) else ∅) := by
    rw [Finset.disjoint_left]
    intro y hy hmem
    obtain ⟨j, _, hj⟩ := Finset.mem_map.mp hy
    by_cases hcond : p = 0 ∧ a + 1 ≤ (maxPos t τ).val
    · rw [ite_eq_left hcond] at hmem
      rw [Finset.mem_singleton.mp hmem] at hj
      exact Fin.succAbove_ne p j hj
    · rw [ite_eq_right hcond] at hmem
      exact Finset.notMem_empty y hmem
  rw [Phi_filter_set, Finset.card_union_of_disjoint hdisj, Finset.card_map]
  congr 1
  by_cases hcond : p = 0 ∧ a + 1 ≤ (maxPos t τ).val
  · rw [ite_eq_left hcond, ite_eq_left hcond, Finset.card_singleton]
  · rw [ite_eq_right hcond, ite_eq_right hcond, Finset.card_empty]

/-- The zero-match condition for `σ = Phi p τ`, in terms of `τ`'s max position. -/
lemma Phi_zero_iff (t a : ℕ) (p : Fin ((t.succ).succ))
    (τ : Equiv.Perm (Fin (t.succ))) :
    ZeroPred (a + 2) (Phi (t.succ) p τ) ↔
      a + 2 ≤ (maxPos t τ).val + (if p.val ≤ (maxPos t τ).val then 1 else 0) + 1 := by
  have hM' := maxPos_max t τ
  have hMσ := Phi_max (t.succ) p τ _ hM'
  rw [zero_of_max _ _ _ _ hMσ, succAbove_val_add]

/-- meshCount change in the high case (`M'(τ) ≥ a + 1`). -/
lemma Phi_mesh_high (t a : ℕ) (p : Fin ((t.succ).succ))
    (τ : Equiv.Perm (Fin (t.succ))) (hu : a + 1 ≤ (maxPos t τ).val) :
    meshN (a + 2) (Phi (t.succ) p τ) = meshN (a + 2) τ + (if p = 0 then 1 else 0) := by
  have hcard := Phi_filter_card_eq t a p τ
  have hzσ : ZeroPred (a + 2) (Phi (t.succ) p τ) := by
    rw [Phi_zero_iff]
    split <;> omega
  have hzτ : ZeroPred (a + 2) τ := by
    rw [zero_of_max _ _ _ _ (maxPos_max t τ)]
    omega
  unfold meshN
  rw [hcard, ite_eq_left hzσ, ite_eq_left hzτ]
  by_cases hp : p = 0
  · have hc : p = 0 ∧ a + 1 ≤ (maxPos t τ).val := ⟨hp, hu⟩
    rw [ite_eq_left hc, ite_eq_left hp]
  · have hc : ¬ (p = 0 ∧ a + 1 ≤ (maxPos t τ).val) := fun h => hp h.1
    rw [ite_eq_right hc, ite_eq_right hp, add_zero]

/-- meshCount change in the middle case (`M'(τ) = a`). -/
lemma Phi_mesh_mid (t a : ℕ) (p : Fin ((t.succ).succ))
    (τ : Equiv.Perm (Fin (t.succ))) (hu : (maxPos t τ).val = a) :
    meshN (a + 2) (Phi (t.succ) p τ) = (if p.val ≤ a then 1 else 0) := by
  have hcard := Phi_filter_card_eq t a p τ
  have hcond : ¬ (p = 0 ∧ a + 1 ≤ (maxPos t τ).val) := by omega
  rw [ite_eq_right hcond, add_zero] at hcard
  have hvan : meshN (a + 2) τ = 0 :=
    vanish_meshN _ _ _ _ (maxPos_max t τ) (by omega)
  have hvan0 : (Finset.univ.filter (MatchPred (a + 2) τ)).card = 0 := by
    unfold meshN at hvan
    omega
  have hz : (if ZeroPred (a + 2) (Phi (t.succ) p τ) then 1 else 0)
      = (if p.val ≤ a then 1 else 0) := by
    by_cases h : p.val ≤ a
    · rw [ite_eq_left h]
      have hzσ : ZeroPred (a + 2) (Phi (t.succ) p τ) := by
        rw [Phi_zero_iff t a p τ, hu, ite_eq_left h]
      rw [ite_eq_left hzσ]
    · rw [ite_eq_right h]
      have hzσ : ¬ ZeroPred (a + 2) (Phi (t.succ) p τ) := by
        rw [Phi_zero_iff t a p τ, hu, ite_eq_right h]
        omega
      rw [ite_eq_right hzσ]
  unfold meshN
  rw [hcard, hvan0, hz]
  simp

/-- meshCount change in the low case (`M'(τ) < a`). -/
lemma Phi_mesh_low (t a : ℕ) (p : Fin ((t.succ).succ))
    (τ : Equiv.Perm (Fin (t.succ))) (hu : (maxPos t τ).val < a) :
    meshN (a + 2) (Phi (t.succ) p τ) = 0 := by
  have hcard := Phi_filter_card_eq t a p τ
  have hcond : ¬ (p = 0 ∧ a + 1 ≤ (maxPos t τ).val) := by omega
  rw [ite_eq_right hcond, add_zero] at hcard
  have hvanτ : meshN (a + 2) τ = 0 :=
    vanish_meshN _ _ _ _ (maxPos_max t τ) (by omega)
  have hzσ : ¬ ZeroPred (a + 2) (Phi (t.succ) p τ) := by
    rw [Phi_zero_iff]
    split <;> omega
  have hcard0 : (Finset.univ.filter (MatchPred (a + 2) τ)).card = 0 := by
    unfold meshN at hvanτ
    omega
  unfold meshN
  rw [hcard, hcard0, ite_eq_right hzσ]

/-- Summing over the insertion position in the high case. -/
lemma high_inner (t a : ℕ) (τ : Equiv.Perm (Fin (t.succ)))
    (hu : a + 1 ≤ (maxPos t τ).val) :
    ∑ p : Fin ((t.succ).succ),
        (Polynomial.X : Polynomial ℕ) ^ meshN (a + 2) (Phi (t.succ) p τ)
      = (Polynomial.X + Polynomial.C (t.succ))
        * (Polynomial.X : Polynomial ℕ) ^ meshN (a + 2) τ := by
  have hC : ((t.succ : ℕ) : Polynomial ℕ) = Polynomial.C (t.succ) := by
    rw [← map_natCast Polynomial.C (t.succ), Nat.cast_id]
  have h0 : meshN (a + 2) (Phi (t.succ) 0 τ) = meshN (a + 2) τ + 1 := by
    rw [Phi_mesh_high t a 0 τ hu, ite_eq_left rfl]
  have hrest : ∀ p ∈ Finset.univ.erase (0 : Fin ((t.succ).succ)),
      (Polynomial.X : Polynomial ℕ) ^ meshN (a + 2) (Phi (t.succ) p τ)
        = (Polynomial.X : Polynomial ℕ) ^ meshN (a + 2) τ := by
    intro p hp
    have hne : p ≠ 0 := Finset.ne_of_mem_erase hp
    rw [Phi_mesh_high t a p τ hu, ite_eq_right hne, add_zero]
  have hcard : (Finset.univ.erase (0 : Fin ((t.succ).succ))).card = t.succ := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin]
    omega
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin ((t.succ).succ))), h0,
    Finset.sum_congr rfl hrest, Finset.sum_const, hcard, nsmul_eq_mul, pow_succ,
    add_mul, mul_comm (Polynomial.X : Polynomial ℕ) _, ← hC]

/-- Summing over the insertion position in the middle case. -/
lemma mid_inner (t a : ℕ) (τ : Equiv.Perm (Fin (t.succ)))
    (hu : (maxPos t τ).val = a) :
    ∑ p : Fin ((t.succ).succ),
        (Polynomial.X : Polynomial ℕ) ^ meshN (a + 2) (Phi (t.succ) p τ)
      = ((Finset.univ.filter (fun p : Fin ((t.succ).succ) => p.val ≤ a)).card)
          • (Polynomial.X : Polynomial ℕ)
        + ((Finset.univ.filter (fun p : Fin ((t.succ).succ) => ¬ p.val ≤ a)).card)
          • (1 : Polynomial ℕ) := by
  have hterm : ∀ p : Fin ((t.succ).succ),
      (Polynomial.X : Polynomial ℕ) ^ meshN (a + 2) (Phi (t.succ) p τ)
        = (if p.val ≤ a then (Polynomial.X : Polynomial ℕ) else 0)
          + (if ¬ p.val ≤ a then (1 : Polynomial ℕ) else 0) := by
    intro p
    rw [Phi_mesh_mid t a p τ hu]
    by_cases h : p.val ≤ a <;> simp [h]
  rw [Finset.sum_congr rfl (fun p _ => hterm p), Finset.sum_add_distrib,
    ← Finset.sum_filter, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const]

/-- Summing over the insertion position in the low case. -/
lemma low_inner (t a : ℕ) (τ : Equiv.Perm (Fin (t.succ)))
    (hu : (maxPos t τ).val < a) :
    ∑ p : Fin ((t.succ).succ),
        (Polynomial.X : Polynomial ℕ) ^ meshN (a + 2) (Phi (t.succ) p τ)
      = ((t.succ).succ) • (1 : Polynomial ℕ) := by
  have hterm : ∀ p : Fin ((t.succ).succ),
      (Polynomial.X : Polynomial ℕ) ^ meshN (a + 2) (Phi (t.succ) p τ) = 1 := by
    intro p
    rw [Phi_mesh_low t a p τ hu]
    exact pow_zero _
  rw [Finset.sum_congr rfl (fun p _ => hterm p), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]

/-- The Stirling-type recursion for the counting polynomial (main step). -/
lemma poly_rec (t a : ℕ) (h : a ≤ t) : PolyN (t.succ.succ) (a + 2)
    = (Polynomial.X + Polynomial.C (t.succ)) * PolyN (t.succ) (a + 2) := by
  have hLHS : PolyN (t.succ.succ) (a + 2)
      = ∑ τ : Equiv.Perm (Fin (t.succ)), ∑ p : Fin ((t.succ).succ),
        (Polynomial.X : Polynomial ℕ) ^ meshN (a + 2) (Phi (t.succ) p τ) := by
    have h1 := poly_reindex (t.succ) (a + 2)
    rw [Fintype.sum_prod_type, Finset.sum_comm] at h1
    exact h1
  have hRHS : (Polynomial.X + Polynomial.C (t.succ)) * PolyN (t.succ) (a + 2)
      = ∑ τ : Equiv.Perm (Fin (t.succ)),
        (Polynomial.X + Polynomial.C (t.succ))
          * (Polynomial.X : Polynomial ℕ) ^ meshN (a + 2) τ := by
    change (Polynomial.X + Polynomial.C (t.succ)) *
      (∑ σ : Equiv.Perm (Fin (t.succ)),
        (Polynomial.X : Polynomial ℕ) ^ meshN (a + 2) σ) = _
    rw [Finset.mul_sum]
  have hsplit : ∀ (f : Equiv.Perm (Fin (t.succ)) → Polynomial ℕ),
      ∑ τ : Equiv.Perm (Fin (t.succ)), f τ
        = (∑ τ ∈ Finset.univ.filter
            (fun τ : Equiv.Perm (Fin (t.succ)) => a + 1 ≤ (maxPos t τ).val), f τ)
          + (∑ τ ∈ Finset.univ.filter
            (fun τ : Equiv.Perm (Fin (t.succ)) => ¬ a + 1 ≤ (maxPos t τ).val), f τ) := by
    intro f
    rw [Finset.sum_filter_add_sum_filter_not]
  rw [hLHS, hRHS, hsplit, hsplit]
  congr 1
  · apply Finset.sum_congr rfl
    intro τ hτ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ
    exact high_inner t a τ hτ
  · have hLowEq : Finset.univ.filter
          (fun τ : Equiv.Perm (Fin (t.succ)) => ¬ a + 1 ≤ (maxPos t τ).val)
        = Finset.univ.filter
          (fun τ : Equiv.Perm (Fin (t.succ)) => (maxPos t τ).val ≤ a) := by
      ext τ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    rw [hLowEq]
    have hmaps : ∀ τ ∈ Finset.univ.filter
        (fun τ : Equiv.Perm (Fin (t.succ)) => (maxPos t τ).val ≤ a),
        (maxPos t τ).val ∈ Finset.range (a + 1) := by
      intro τ hτ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_range] at hτ ⊢
      omega
    have hfibS := Finset.sum_fiberwise_of_maps_to hmaps
      (fun τ : Equiv.Perm (Fin (t.succ)) => ∑ p : Fin ((t.succ).succ),
        (Polynomial.X : Polynomial ℕ) ^ meshN (a + 2) (Phi (t.succ) p τ))
    have hfibR := Finset.sum_fiberwise_of_maps_to hmaps
      (fun τ : Equiv.Perm (Fin (t.succ)) =>
        (Polynomial.X + Polynomial.C (t.succ))
          * (Polynomial.X : Polynomial ℕ) ^ meshN (a + 2) τ)
    have hred : ∀ u ∈ Finset.range (a + 1),
        (Finset.univ.filter
          (fun τ : Equiv.Perm (Fin (t.succ)) => (maxPos t τ).val ≤ a)).filter
          (fun τ => (maxPos t τ).val = u)
        = Finset.univ.filter
          (fun τ : Equiv.Perm (Fin (t.succ)) => (maxPos t τ).val = u) := by
      intro u hu
      ext τ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨-, h2⟩
        exact h2
      · intro h2
        refine ⟨?_, h2⟩
        simp only [Finset.mem_range] at hu
        omega
    have hTotS : (∑ τ ∈ Finset.univ.filter
          (fun τ : Equiv.Perm (Fin (t.succ)) => (maxPos t τ).val ≤ a),
          ∑ p : Fin ((t.succ).succ),
          (Polynomial.X : Polynomial ℕ) ^ meshN (a + 2) (Phi (t.succ) p τ))
        = a • ((Nat.factorial t)
            • ((((t.succ).succ : ℕ)) • (1 : Polynomial ℕ)))
          + (Nat.factorial t)
            • ((a + 1) • (Polynomial.X : Polynomial ℕ)
              + (Finset.univ.filter
                (fun p : Fin ((t.succ).succ) => ¬ p.val ≤ a)).card
                • (1 : Polynomial ℕ)) := by
      rw [← hfibS]
      show (∑ u ∈ Finset.range (a + 1), ∑ τ ∈ (Finset.univ.filter
        (fun τ : Equiv.Perm (Fin (t.succ)) => (maxPos t τ).val ≤ a)).filter
        (fun τ => (maxPos t τ).val = u),
        ∑ p : Fin ((t.succ).succ),
        (Polynomial.X : Polynomial ℕ) ^ meshN (a + 2) (Phi (t.succ) p τ)) = _
      rw [Finset.sum_range_succ]
      congr 1
      · have hconst : ∀ u ∈ Finset.range a,
            (∑ τ ∈ (Finset.univ.filter
              (fun τ : Equiv.Perm (Fin (t.succ)) => (maxPos t τ).val ≤ a)).filter
              (fun τ => (maxPos t τ).val = u),
              ∑ p : Fin ((t.succ).succ),
              (Polynomial.X : Polynomial ℕ) ^ meshN (a + 2) (Phi (t.succ) p τ))
            = (Nat.factorial t) • ((((t.succ).succ : ℕ)) • (1 : Polynomial ℕ)) := by
          intro u hu
          have hu' : u ∈ Finset.range (a + 1) := by
            simp only [Finset.mem_range] at hu ⊢
            omega
          rw [hred u hu']
          have hterm : ∀ τ ∈ Finset.univ.filter
              (fun τ : Equiv.Perm (Fin (t.succ)) => (maxPos t τ).val = u),
              (∑ p : Fin ((t.succ).succ),
                (Polynomial.X : Polynomial ℕ) ^ meshN (a + 2) (Phi (t.succ) p τ))
              = ((((t.succ).succ : ℕ)) • (1 : Polynomial ℕ)) := by
            intro τ hτ
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ
            simp only [Finset.mem_range] at hu
            have hlt : (maxPos t τ).val < a := by omega
            exact low_inner t a τ hlt
          rw [Finset.sum_congr rfl hterm, Finset.sum_const,
            fiber_card t u (by simp only [Finset.mem_range] at hu; omega)]
        rw [Finset.sum_eq_card_nsmul hconst, Finset.card_range]
      · show (∑ τ ∈ (Finset.univ.filter
          (fun τ : Equiv.Perm (Fin (t.succ)) => (maxPos t τ).val ≤ a)).filter
          (fun τ => (maxPos t τ).val = a),
          ∑ p : Fin ((t.succ).succ),
          (Polynomial.X : Polynomial ℕ) ^ meshN (a + 2) (Phi (t.succ) p τ)) = _
        rw [hred a (by simp only [Finset.mem_range]; omega)]
        have htermM : ∀ τ ∈ Finset.univ.filter
            (fun τ : Equiv.Perm (Fin (t.succ)) => (maxPos t τ).val = a),
            (∑ p : Fin ((t.succ).succ),
              (Polynomial.X : Polynomial ℕ) ^ meshN (a + 2) (Phi (t.succ) p τ))
            = ((Finset.univ.filter (fun p : Fin ((t.succ).succ) => p.val ≤ a)).card)
                • (Polynomial.X : Polynomial ℕ)
              + ((Finset.univ.filter
                (fun p : Fin ((t.succ).succ) => ¬ p.val ≤ a)).card)
                • (1 : Polynomial ℕ) := by
          intro τ hτ
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ
          exact mid_inner t a τ hτ
        rw [Finset.sum_congr rfl htermM, Finset.sum_const,
          fiber_card t a (by omega), filter_le_card t a h]
    have hTotR : (∑ τ ∈ Finset.univ.filter
          (fun τ : Equiv.Perm (Fin (t.succ)) => (maxPos t τ).val ≤ a),
          (Polynomial.X + Polynomial.C (t.succ))
            * (Polynomial.X : Polynomial ℕ) ^ meshN (a + 2) τ)
        = ((a + 1) * Nat.factorial t)
          • ((Polynomial.X + Polynomial.C (t.succ))) := by
      rw [← hfibR]
      show (∑ u ∈ Finset.range (a + 1), ∑ τ ∈ (Finset.univ.filter
        (fun τ : Equiv.Perm (Fin (t.succ)) => (maxPos t τ).val ≤ a)).filter
        (fun τ => (maxPos t τ).val = u),
        (Polynomial.X + Polynomial.C (t.succ))
          * (Polynomial.X : Polynomial ℕ) ^ meshN (a + 2) τ) = _
      have hconstR : ∀ u ∈ Finset.range (a + 1),
          (∑ τ ∈ (Finset.univ.filter
            (fun τ : Equiv.Perm (Fin (t.succ)) => (maxPos t τ).val ≤ a)).filter
            (fun τ => (maxPos t τ).val = u),
            (Polynomial.X + Polynomial.C (t.succ))
              * (Polynomial.X : Polynomial ℕ) ^ meshN (a + 2) τ)
          = (Nat.factorial t) • (Polynomial.X + Polynomial.C (t.succ)) := by
        intro u hu
        rw [hred u hu]
        have htermR : ∀ τ ∈ Finset.univ.filter
            (fun τ : Equiv.Perm (Fin (t.succ)) => (maxPos t τ).val = u),
            (Polynomial.X + Polynomial.C (t.succ))
              * (Polynomial.X : Polynomial ℕ) ^ meshN (a + 2) τ
            = (Polynomial.X + Polynomial.C (t.succ)) := by
          intro τ hτ
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ
          simp only [Finset.mem_range] at hu
          have hc0 : meshN (a + 2) τ = 0 :=
            vanish_meshN _ _ _ _ (maxPos_max t τ) (by omega)
          rw [hc0, pow_zero, mul_one]
        rw [Finset.sum_congr rfl htermR, Finset.sum_const,
          fiber_card t u (by simp only [Finset.mem_range] at hu; omega)]
      rw [Finset.sum_eq_card_nsmul hconstR, Finset.card_range]
      simp only [nsmul_eq_mul, Nat.cast_mul, mul_assoc]
    rw [hTotS, hTotR]
    have hC : ((t.succ : ℕ) : Polynomial ℕ) = Polynomial.C (t.succ) := by
      rw [← map_natCast Polynomial.C (t.succ), Nat.cast_id]
    exact aggregate_identity a (t.succ)
      (Finset.univ.filter (fun p : Fin ((t.succ).succ) => ¬ p.val ≤ a)).card
      (Nat.factorial t) (Polynomial.X) (Polynomial.C (t.succ)) hC
      (filter_card_add t a h)

/--
The counting polynomial for the quadrant marked mesh pattern satisfies a Stirling-type recursion,
together with its coefficient recurrence and initial value.

Source: Matt Davis, "Quadrant Marked Mesh Patterns and the r-Stirling Numbers," Journal
of Integer Sequences 18 (2015), Article 15.10.1, Theorem (label `thm:main`), line 175,
<https://cs.uwaterloo.ca/journals/JIS/VOL18/Davis/davis3.tex>.

Proves `Wanted` entry `meshPatternCount_stirlingRecursion`.
-/
theorem meshPatternCount_stirlingRecursion
    (k n j : ℕ) (hk : 1 < k) (hn : k ≤ n) (hj : 0 < j) :
    let isMeshMatch : {m : ℕ} → ℕ → Equiv.Perm (Fin m) → Fin m → Prop :=
      fun {m} r σ i =>
        ∃ maxIndex : Fin m,
          (∀ t : Fin m, σ t ≤ σ maxIndex) ∧
          r - 1 ≤ (Finset.univ.filter fun t : Fin m =>
            i < t ∧ t < maxIndex ∧ σ i < σ t).card ∧
          ∀ t : Fin m, t < i → σ t < σ i
    let zeroMatches : {m : ℕ} → ℕ → Equiv.Perm (Fin m) → Prop :=
      fun {m} r σ =>
        ∃ maxIndex : Fin m,
          (∀ t : Fin m, σ t ≤ σ maxIndex) ∧ r ≤ maxIndex.val + 1
    let meshCount : {m : ℕ} → ℕ → Equiv.Perm (Fin m) → ℕ :=
      fun {_m} r σ =>
        (Finset.univ.filter (isMeshMatch r σ)).card + if zeroMatches r σ then 1 else 0
    let P : ℕ → ℕ → Polynomial ℕ := fun m r =>
      ∑ σ : Equiv.Perm (Fin m), Polynomial.X ^ meshCount r σ
    let C : ℕ → ℕ → ℕ → ℕ := fun m r s => (P m r).coeff s
    C n k j = (n - 1) * C (n - 1) k j + C (n - 1) k (j - 1) ∧
      P n k = (Polynomial.X + Polynomial.C (n - 1)) * P (n - 1) k ∧
      C n k 0 = (n - 1) * C (n - 1) k 0 ∧
      P (k - 1) k = Polynomial.C (Nat.factorial (k - 1)) := by
  intro isMeshMatch zeroMatches meshCount P C
  have hM : ∀ {m : ℕ} (r : ℕ) (σ : Equiv.Perm (Fin m)) (i : Fin m),
      isMeshMatch r σ i = MatchPred r σ i := fun _ _ _ => rfl
  have hZ : ∀ {m : ℕ} (r : ℕ) (σ : Equiv.Perm (Fin m)),
      zeroMatches r σ = ZeroPred r σ := fun _ _ => rfl
  have hmesh : ∀ {m : ℕ} (r : ℕ) (σ : Equiv.Perm (Fin m)),
      meshCount r σ = meshN r σ := fun _ _ => rfl
  have hP : ∀ (m r : ℕ), P m r = PolyN m r := fun _ _ => rfl
  have hC : ∀ (m r s : ℕ), C m r s = CoefN m r s := fun _ _ _ => rfl
  simp only [hP, hC]
  obtain ⟨m₀, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m₀ ≠ 0)
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le (show 2 ≤ k by omega)
  rw [add_comm (2 : ℕ) a]
  obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  have hRec : PolyN (t.succ.succ) (a + 2)
      = (Polynomial.X + Polynomial.C (t.succ.succ - 1))
        * PolyN (t.succ.succ - 1) (a + 2) :=
    poly_rec t a (by omega)
  rw [Nat.succ_eq_add_one j', Nat.add_sub_cancel]
  refine ⟨?_, hRec, ?_, base_poly (a + 2) (by omega)⟩
  · unfold CoefN
    rw [hRec, coeff_rec_succ]
    exact add_comm _ _
  · unfold CoefN
    rw [hRec]
    exact coeff_rec_zero _ _

end MetaMathlibExt
end

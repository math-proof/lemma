import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.VandermondeTypeConvolutionForSRestrictedWeightedCompositions
open scoped BigOperators
open MathlibExt.Combinatorics.Enumerative


namespace MathlibExt.Combinatorics.Enumerative

/--
[vandermondeTypeConvolutionForSRestrictedWeightedCompositions](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/VandermondeTypeConvolutionForSRestrictedWeightedCompositions.lean)
-/
@[path]
lemma vandermondeTypeConvolutionForSRestrictedWeightedCompositions
  [CommRing R]
  {S : Finset ℕ}
  {f : ℕ → R}
  {n k j : ℕ}
-- given
  (hj : j ≤ k) :
-- imply
  sRestrictedWeightedCompositionCount S f n k =
    ∑ m ∈ Finset.range (n + 1),
    sRestrictedWeightedCompositionCount S f m j *
    sRestrictedWeightedCompositionCount S f (n - m) (k - j) := by
-- proof
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
  have hsub : j + d - j = d := by
    omega
  rw [hsub]
  classical
  unfold sRestrictedWeightedCompositionCount
  have hle : ∀ (jj nn : ℕ) (σ : Fin jj → Fin (nn + 1)) (i : Fin jj),
    (σ i : ℕ) ≤ ∑ k, (σ k : ℕ) := by
    intro jj nn σ i
    have h0 : ∀ x ∈ Finset.univ, 0 ≤ (σ x : ℕ) := by
      intro x h
      exact Nat.zero_le _
    have h1 := Finset.single_le_sum h0 (Finset.mem_univ i)
    exact h1
  have hcount : ∀ (kk mm nn : ℕ) (hm : mm ≤ nn),
    (∑ τ ∈ Finset.univ.filter
      (fun τ : Fin kk → Fin (mm + 1) => (∀ i, (τ i : ℕ) ∈ S) ∧ ∑ i, (τ i : ℕ) = mm),
      ∏ i, f (τ i)) =
    (∑ σ ∈ Finset.univ.filter
      (fun σ : Fin kk → Fin (nn + 1) => (∀ i, (σ i : ℕ) ∈ S) ∧ ∑ i, (σ i : ℕ) = mm),
      ∏ i, f (σ i)) := by
    intro kk mm nn hm
    have hle1 : mm + 1 ≤ nn + 1 := by
      omega
    apply Finset.sum_bij (fun τ _ i => Fin.castLE hle1 (τ i))
    · intro τ hτ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
      have hS := hτ.1
      have hsum := hτ.2
      constructor
      · intro i
        have hs := hS i
        simp only [Fin.val_castLE]
        exact hs
      · simp only [Fin.val_castLE]
        exact hsum
    · intro τ1 h1 τ2 h2 heq
      apply funext
      intro i
      have heqi := congrFun heq i
      have hval := congrArg (fun x : Fin (nn + 1) => (x : ℕ)) heqi
      simp only [Fin.val_castLE] at hval
      exact Fin.ext hval
    · intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
      have hS := hσ.1
      have hsum := hσ.2
      have hbound : ∀ i, (σ i : ℕ) < mm + 1 := by
        intro i
        have hle_i := hle kk nn σ i
        omega
      refine ⟨fun i => ⟨(σ i : ℕ), hbound i⟩, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro i
          exact hS i
        · exact hsum
      · apply funext
        intro i
        apply Fin.ext
        exact Fin.val_castLE hle1 _
    · intro τ hτ
      apply Finset.prod_congr rfl
      intro i h
      simp only [Fin.val_castLE]
  have hrwJ : ∀ m ∈ Finset.range (n + 1),
    (∑ π ∈ Finset.univ.filter
      (fun π : Fin j → Fin (m + 1) => (∀ i, (π i : ℕ) ∈ S) ∧ ∑ i, (π i : ℕ) = m),
      ∏ i, f (π i)) =
    (∑ π ∈ Finset.univ.filter
      (fun π : Fin j → Fin (n + 1) => (∀ i, (π i : ℕ) ∈ S) ∧ ∑ i, (π i : ℕ) = m),
      ∏ i, f (π i)) := by
    intro m hm
    have hm_lt := Finset.mem_range.mp hm
    have hm_le : m ≤ n := by
      omega
    exact hcount j m n hm_le
  have hrwD : ∀ m ∈ Finset.range (n + 1),
    (∑ π ∈ Finset.univ.filter
      (fun π : Fin d → Fin (n - m + 1) => (∀ i, (π i : ℕ) ∈ S) ∧ ∑ i, (π i : ℕ) = n - m),
      ∏ i, f (π i)) =
    (∑ π ∈ Finset.univ.filter
      (fun π : Fin d → Fin (n + 1) => (∀ i, (π i : ℕ) ∈ S) ∧ ∑ i, (π i : ℕ) = n - m),
      ∏ i, f (π i)) := by
    intro m hm
    have hle : n - m ≤ n := by
      omega
    exact hcount d (n - m) n hle
  have hRHS : (∑ m ∈ Finset.range (n + 1),
    (∑ π ∈ Finset.univ.filter
      (fun π : Fin j → Fin (m + 1) => (∀ i, (π i : ℕ) ∈ S) ∧ ∑ i, (π i : ℕ) = m),
      ∏ i, f (π i)) *
    (∑ π ∈ Finset.univ.filter
      (fun π : Fin d → Fin (n - m + 1) => (∀ i, (π i : ℕ) ∈ S) ∧ ∑ i, (π i : ℕ) = n - m),
      ∏ i, f (π i))) =
    (∑ m ∈ Finset.range (n + 1),
      (∑ π ∈ Finset.univ.filter
        (fun π : Fin j → Fin (n + 1) => (∀ i, (π i : ℕ) ∈ S) ∧ ∑ i, (π i : ℕ) = m),
        ∏ i, f (π i)) *
      (∑ π ∈ Finset.univ.filter
        (fun π : Fin d → Fin (n + 1) => (∀ i, (π i : ℕ) ∈ S) ∧ ∑ i, (π i : ℕ) = n - m),
        ∏ i, f (π i))) := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [hrwJ m hm, hrwD m hm]
  rw [hRHS]
  set e : Fin j ⊕ Fin d ≃ Fin (j + d) := finSumFinEquiv with he
  have hsplit : (∑ π ∈ Finset.univ.filter
    (fun π : Fin (j + d) → Fin (n + 1) => (∀ i, (π i : ℕ) ∈ S) ∧ ∑ i, (π i : ℕ) = n),
    ∏ i, f (π i)) =
    (∑ p ∈ (Finset.univ ×ˢ Finset.univ).filter
      (fun p : (Fin j → Fin (n + 1)) × (Fin d → Fin (n + 1)) =>
        ((∀ i, (p.1 i : ℕ) ∈ S) ∧ (∀ i, (p.2 i : ℕ) ∈ S)) ∧
          (∑ i, (p.1 i : ℕ)) + (∑ i, (p.2 i : ℕ)) = n),
      (∏ i, f (p.1 i)) * (∏ i, f (p.2 i))) := by
    apply Finset.sum_bij
      (fun π _ => (fun i => π (e (Sum.inl i)), fun i => π (e (Sum.inr i))))
    · intro π hπ
      simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_product, true_and] at hπ ⊢
      have hS := hπ.1
      have hsum := hπ.2
      constructor
      · constructor
        · intro i
          exact hS _
        · intro i
          exact hS _
      · have h1 := Function.Bijective.sum_comp e.bijective (fun k : Fin (j + d) => (π k : ℕ))
        have h2 := Fintype.sum_sum_type (fun x : Fin j ⊕ Fin d => (π (e x) : ℕ))
        have hsplit_sum : ∑ i, (π i : ℕ) =
          (∑ i, (π (e (Sum.inl i)) : ℕ)) + (∑ i, (π (e (Sum.inr i)) : ℕ)) := by
          exact h1.symm.trans h2
        exact hsplit_sum.symm.trans hsum
    · intro π1 h1 π2 h2 heq
      have hfst := congrArg Prod.fst heq
      have hsnd := congrArg Prod.snd heq
      apply funext
      intro k
      have hk2 : e (e.symm k) = k :=
        e.apply_symm_apply k
      rw [← hk2]
      cases e.symm k with
      | inl a =>
        have hfa := congrFun hfst a
        exact hfa
      | inr b =>
        have hfb := congrFun hsnd b
        exact hfb
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hp
      have hS1 := hp.1.1
      have hS2 := hp.1.2
      have hsum := hp.2
      refine ⟨fun k => Sum.elim p.1 p.2 (e.symm k), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro k
          cases e.symm k with
          | inl a =>
            exact hS1 a
          | inr b =>
            exact hS2 b
        · have hsum_eq : ∑ k, Sum.elim (fun i => (p.1 i : ℕ)) (fun i => (p.2 i : ℕ)) (e.symm k) =
          (∑ i, (p.1 i : ℕ)) + (∑ i, (p.2 i : ℕ)) := by
          have h1 := Function.Bijective.sum_comp e.bijective
            (fun k : Fin (j + d) =>
              Sum.elim (fun i => (p.1 i : ℕ)) (fun i => (p.2 i : ℕ)) (e.symm k))
          have h2 := Fintype.sum_sum_type
            (fun x : Fin j ⊕ Fin d => Sum.elim (fun i => (p.1 i : ℕ)) (fun i => (p.2 i : ℕ)) x)
          have h4 : (∑ x, Sum.elim (fun i => (p.1 i : ℕ)) (fun i => (p.2 i : ℕ)) (e.symm (e x))) =
            (∑ x, Sum.elim (fun i => (p.1 i : ℕ)) (fun i => (p.2 i : ℕ)) x) := by
            simp only [e.symm_apply_apply]
          exact h1.symm.trans (h4.trans h2)
          have hbridge : (∑ k, Sum.elim (fun i => (p.1 i : ℕ)) (fun i => (p.2 i : ℕ)) (e.symm k)) =
            (∑ x, (((Sum.elim p.1 p.2 (e.symm x) : Fin (n + 1))) : ℕ)) := by
            apply Finset.sum_congr rfl
            intro k _
            cases h : e.symm k with
            | inl a => rfl
            | inr b => rfl
          rw [← hbridge]
          exact hsum_eq.trans hsum
      · apply Prod.ext
        · apply funext
          intro i
          simp only [e.symm_apply_apply, Sum.elim_inl]
        · apply funext
          intro i
          simp only [e.symm_apply_apply, Sum.elim_inr]
    · intro π hπ
      have h1 := Equiv.prod_comp e (fun k : Fin (j + d) => f (π k))
      have h2 := Fintype.prod_sum_type (fun x : Fin j ⊕ Fin d => f (π (e x)))
      exact h1.symm.trans h2
  rw [hsplit]
  have hmaps : ∀ p ∈ (Finset.univ ×ˢ Finset.univ).filter
    (fun p : (Fin j → Fin (n + 1)) × (Fin d → Fin (n + 1)) =>
      ((∀ i, (p.1 i : ℕ) ∈ S) ∧ (∀ i, (p.2 i : ℕ) ∈ S)) ∧
        (∑ i, (p.1 i : ℕ)) + (∑ i, (p.2 i : ℕ)) = n),
    (∑ i, (p.1 i : ℕ)) ∈ Finset.range (n + 1) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hp
    have hsum := hp.2
    rw [Finset.mem_range]
    omega
  have hfiber : ∀ m ∈ Finset.range (n + 1),
    ((Finset.univ ×ˢ Finset.univ).filter
      (fun p : (Fin j → Fin (n + 1)) × (Fin d → Fin (n + 1)) =>
        ((∀ i, (p.1 i : ℕ) ∈ S) ∧ (∀ i, (p.2 i : ℕ) ∈ S)) ∧
          (∑ i, (p.1 i : ℕ)) + (∑ i, (p.2 i : ℕ)) = n)).filter
      (fun p => (∑ i, (p.1 i : ℕ)) = m) =
    (Finset.univ.filter
      (fun σ : Fin j → Fin (n + 1) => (∀ i, (σ i : ℕ) ∈ S) ∧ ∑ i, (σ i : ℕ) = m)) ×ˢ
    (Finset.univ.filter
      (fun τ : Fin d → Fin (n + 1) => (∀ i, (τ i : ℕ) ∈ S) ∧ ∑ i, (τ i : ℕ) = n - m)) := by
    intro m hm
    have hm_lt := Finset.mem_range.mp hm
    have hm_le : m ≤ n := by
      omega
    apply Finset.ext
    intro p
    cases p with
    | mk σ τ =>
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
      constructor
      · intro h
        have hA := h.1.1.1
        have hB := h.1.1.2
        have hC := h.1.2
        have hD := h.2
        have hE : (∑ i, (τ i : ℕ)) = n - m := by
          omega
        exact ⟨⟨hA, hD⟩, ⟨hB, hE⟩⟩
      · intro h
        have hA := h.1.1
        have hD := h.1.2
        have hB := h.2.1
        have hE := h.2.2
        have hC : (∑ i, (σ i : ℕ)) + (∑ i, (τ i : ℕ)) = n := by
          omega
        exact ⟨⟨⟨hA, hB⟩, hC⟩, hD⟩
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps
    (fun p : (Fin j → Fin (n + 1)) × (Fin d → Fin (n + 1)) =>
      (∏ i, f (p.1 i)) * (∏ i, f (p.2 i)))
  rw [← hfib]
  apply Finset.sum_congr rfl
  intro m hm
  rw [hfiber m hm]
  rw [Finset.sum_product, Finset.sum_mul_sum]

end MathlibExt.Combinatorics.Enumerative


-- created on 2026-10-20
-- updated on 2026-10-26

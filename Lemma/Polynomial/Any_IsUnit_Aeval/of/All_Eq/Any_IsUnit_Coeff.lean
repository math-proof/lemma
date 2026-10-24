import Mathlib
import sympy.Basic
open Polynomial IsLocalRing


private lemma exists_isUnit_aeval
  {R : Type u}
  [CommRing R]
  {S : Type u}
  [CommRing S]
  [Algebra R S]
  [IsLocalRing S]
  (D : Polynomial R) (hD : ∃ i, IsUnit (D.coeff i))
  (x : Fin (D.natDegree + 1) → S) (hx : ∀ i j, x i - x j ∈ IsLocalRing.maximalIdeal S → i = j) :
  ∃ i, IsUnit (Polynomial.aeval (x i) D) := by
  classical
  set φ : R →+* IsLocalRing.ResidueField S := (IsLocalRing.residue S).comp (algebraMap R S) with hφ
  set Dbar : Polynomial (IsLocalRing.ResidueField S) := D.map φ with hDbar
  have hDbar0 : Dbar ≠ 0 := by
    obtain ⟨i, hi⟩ := hD
    intro h
    have hc : Dbar.coeff i = 0 := by rw [h, coeff_zero]
    rw [hDbar, coeff_map] at hc
    exact (hi.map φ).ne_zero hc
  have hdeg : Dbar.natDegree ≤ D.natDegree := natDegree_map_le
  set xb : Fin (D.natDegree + 1) → IsLocalRing.ResidueField S := fun i => IsLocalRing.residue S (x i) with hxb
  have hxb_inj : Function.Injective xb := by
    intro i j h
    apply hx i j
    rwa [← Ideal.Quotient.eq]
  by_contra hcon
  have hcon' : ∀ i, ¬ IsUnit (Polynomial.aeval (x i) D) := fun i h => hcon ⟨i, h⟩
  have hroot : ∀ i, Dbar.IsRoot (xb i) := by
    intro i
    have h1 : Polynomial.aeval (x i) D ∈ IsLocalRing.maximalIdeal S :=
      (IsLocalRing.mem_maximalIdeal _).mpr (hcon' i)
    have h2 : IsLocalRing.residue S (Polynomial.aeval (x i) D) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr h1
    rw [IsRoot.def, hDbar, eval_map, hxb]
    rwa [aeval_def, hom_eval₂] at h2
  have hsub : (Finset.univ.image xb).val ⊆ Dbar.roots := by
    intro y hy
    rw [Finset.image_val] at hy
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp (Multiset.mem_dedup.mp hy)
    exact (mem_roots hDbar0).mpr (hroot i)
  have hcard := card_le_degree_of_subset_roots hsub
  rw [Finset.card_image_of_injective _ hxb_inj, Finset.card_univ, Fintype.card_fin] at hcard
  omega
/--
[Polynomial_exists_isUnit_aeval_of_sub_mem_maximalIdeal_imp_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Polynomial_exists_isUnit_aeval_of_sub_mem_maximalIdeal_imp_eq.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R]
  {S : Type u} [CommRing S] [Algebra R S] [IsLocalRing S]
  {D : Polynomial R}
  {x : Fin (D.natDegree + 1) → S}
-- given
  (hD : ∃ i, IsUnit (D.coeff i))
  (hx : ∀ i j, x i - x j ∈ IsLocalRing.maximalIdeal S → i = j) :
-- imply
  ∃ i, IsUnit (Polynomial.aeval (x i) D) :=
-- proof
  exists_isUnit_aeval D hD x hx


-- created on 2026-10-23

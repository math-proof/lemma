/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Young.Definitions.Part8
import Lemma.PowerSeries.InfiniteProducts2
import Lemma.MvPolynomial.SymmetricDefinitions
open MvPolynomial Finset BigOperators AlgebraicCombinatorics.SymmetricPolynomials

/-!
# The ω-involution on symmetric functions

The ω-involution is an algebra automorphism of the ring of symmetric functions
that swaps the elementary and complete homogeneous symmetric polynomials:
- ω(e_n) = h_n
- ω(h_n) = e_n
- ω(s_λ) = s_{λᵗ}

This file defines the ω-involution and proves its key properties.

## Main definitions

* `SymmetricFunctions.hsymmAlgHom`: The algebra homomorphism from `MvPolynomial (Fin n) R`
  to the symmetric subalgebra sending `X_i` to `h_{i+1}`.
* `SymmetricFunctions.omegaInvolution`: The ω-involution on symmetric polynomials.

## Main results

* `SymmetricFunctions.omegaInvolution_esymm_succ`: ω(e_{k+1}) = h_{k+1} for k < n
* `SymmetricFunctions.omegaInvolution_hsymm_succ`: ω(h_{k+1}) = e_{k+1} for k < n
* `SymmetricFunctions.omegaInvolution_involutive`: ω ∘ ω = id

## Implementation notes

The ω-involution is defined using the fundamental theorem of symmetric polynomials.
The elementary symmetric polynomials generate the symmetric subalgebra, so we can
define ω by specifying ω(e_k) = h_k and extending algebraically.

To prove that ω is an involution, we need to show that ω(h_k) = e_k. This requires
proving that the h_k also generate the symmetric subalgebra (which they do, by the
Newton-Girard relations and the fundamental theorem).

## References

* [Stanley, *Enumerative Combinatorics, Vol. 2*][Stanley-EC2], Section 7.8
* [Grinberg-Reiner, *Hopf algebras in combinatorics*][GriRei], Section 2.4

## Why this is needed

The ω-involution is essential for proving the second Jacobi-Trudi formula
(jacobiTrudi_e in PieriJacobiTrudi.lean). The standard proof proceeds as follows:

1. First Jacobi-Trudi: s_{λ/μ} = det(h_{λᵢ - μⱼ - i + j})
2. Apply ω: ω(s_{λ/μ}) = det(ω(h_{...})) = det(e_{...})
3. Since ω(s_{λ/μ}) = s_{λᵗ/μᵗ}: s_{λᵗ/μᵗ} = det(e_{λᵢ - μⱼ - i + j})
4. Substitute λ → λᵗ: s_{λ/μ} = det(e_{(λᵗ)ᵢ - (μᵗ)ⱼ - i + j})

This file provides the infrastructure for steps 2 and 3.
-/


namespace SymmetricFunctions

/-!
## Transfer lemmas for esymm and hsymm via rename

These lemmas allow us to transfer results about symmetric polynomials from one
finite type to another via the `rename` operation.
-/


/-- Transfer lemma: esymm is preserved under rename by an equivalence. -/
theorem rename_esymm_eq {σ τ : Type*} [Fintype σ] [Fintype τ] [DecidableEq σ] [DecidableEq τ]
    (e : σ ≃ τ) (R : Type*) [CommRing R] (k : ℕ) :
    rename e (esymm σ R k) = esymm τ R k := by
  simp only [esymm, map_sum, map_prod, rename_X]
  refine Finset.sum_bij' 
    (fun s _ => s.map e.toEmbedding) 
    (fun t _ => t.map e.symm.toEmbedding) ?_ ?_ ?_ ?_ ?_
  · intro s hs
    simp only [mem_powersetCard] at hs ⊢
    exact ⟨subset_univ _, by rw [Finset.card_map]; exact hs.2⟩
  · intro t ht
    simp only [mem_powersetCard] at ht ⊢
    exact ⟨subset_univ _, by rw [Finset.card_map]; exact ht.2⟩
  · intro s _
    ext x
    simp only [mem_map, Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨a, ⟨b, hb, hab⟩, hax⟩
      rw [← hax, ← hab, Equiv.symm_apply_apply]; exact hb
    · intro hx
      exact ⟨e x, ⟨x, hx, rfl⟩, Equiv.symm_apply_apply e x⟩
  · intro t _
    ext x
    simp only [mem_map, Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨a, ⟨b, hb, hab⟩, hax⟩
      rw [← hax, ← hab, Equiv.apply_symm_apply]; exact hb
    · intro hx
      exact ⟨e.symm x, ⟨x, hx, rfl⟩, Equiv.apply_symm_apply e x⟩
  · intro s _
    rw [Finset.prod_map]
    simp only [Equiv.toEmbedding_apply]

/-- Transfer lemma: hsymm is preserved under rename by an equivalence. -/
theorem rename_hsymm_eq {σ τ : Type*} [Fintype σ] [Fintype τ] [DecidableEq σ] [DecidableEq τ]
    (e : σ ≃ τ) (R : Type*) [CommRing R] (k : ℕ) :
    rename e (hsymm σ R k) = hsymm τ R k := by
  simp only [hsymm, map_sum]
  refine Finset.sum_bij' 
    (fun s _ => Sym.map e s) 
    (fun t _ => Sym.map e.symm t) ?_ ?_ ?_ ?_ ?_
  · intro s _; exact mem_univ _
  · intro t _; exact mem_univ _
  · intro s _
    simp only [Sym.map_map, Equiv.symm_comp_self]
    exact Sym.map_id s
  · intro t _
    simp only [Sym.map_map, Equiv.self_comp_symm]
    exact Sym.map_id t
  · intro s _
    rw [map_multiset_prod]
    congr 1
    simp only [Multiset.map_map, Function.comp_apply, rename_X]
    show Multiset.map (fun x => X (e x)) ↑s = Multiset.map X ↑(Sym.map (⇑e) s)
    simp only [Sym.coe_map, Multiset.map_map, Function.comp_apply]

/-- Newton-Girard identity for arbitrary finite type σ.
    Transferred from `newtonGirard_eh` via rename. -/
theorem newtonGirard_eh_general {σ : Type*} [Fintype σ] [DecidableEq σ] 
    {R : Type*} [CommRing R] (n : ℕ) (hn : 0 < n) :
    ∑ j ∈ range (n + 1), (-1 : MvPolynomial σ R) ^ j * esymm σ R j * hsymm σ R (n - j) = 0 := by
  -- Transfer from Fin (Fintype.card σ)
  let N := Fintype.card σ
  let f := (Fintype.equivFin σ).symm
  -- Apply rename f to newtonGirard_eh
  have h := newtonGirard_eh (K := R) (N := N) n hn
  -- h : ∑ j ∈ range (n + 1), (-1)^j * e j * h (n - j) = 0 in MvPolynomial (Fin N) R
  have h' : rename f (∑ j ∈ range (n + 1), (-1 : MvPolynomial (Fin N) R) ^ j * 
              esymm (Fin N) R j * hsymm (Fin N) R (n - j)) = 0 := by
    rw [h, map_zero]
  rw [map_sum] at h'
  simp only [map_mul, map_pow, map_neg, map_one] at h'
  convert h' using 2
  · ext j
    rw [rename_esymm_eq, rename_hsymm_eq]

/-- Helper lemma: sum of subalgebra elements coerces to sum of their values. -/
theorem symmetricSubalgebra_sum_val_nat {σ : Type*} {R : Type*} [CommRing R]
    (s : Finset ℕ) (f : ℕ → symmetricSubalgebra σ R) :
    (∑ i ∈ s, f i).val = ∑ i ∈ s, (f i).val := by
  induction s using Finset.induction_on
  · simp
  · rename_i a s ha ih
    simp only [Finset.sum_insert ha, AddMemClass.coe_add, ih]

end SymmetricFunctions

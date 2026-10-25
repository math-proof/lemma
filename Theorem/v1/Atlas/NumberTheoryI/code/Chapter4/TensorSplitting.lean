/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter4/TensorSplitting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open Polynomial TensorProduct


noncomputable section

namespace TensorSplitting

lemma span_prod_eq_biInf {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (g : ι → R)
    (hc : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (g i) (g j)) :
    Ideal.span ({∏ i ∈ s, g i} : Set R) = ⨅ i ∈ s, Ideal.span ({g i} : Set R) := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    have hc_s : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (g i) (g j) :=
      fun i hi j hj hij =>
        hc i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    rw [Finset.prod_insert ha, Finset.iInf_insert]
    have h_coprime : IsCoprime (g a) (∏ i ∈ s, g i) := by
      apply IsCoprime.prod_right
      intro i hi
      exact hc a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
        (fun h => ha (h ▸ hi))
    rw [← ih hc_s, ← Ideal.span_singleton_mul_span_singleton]
    exact Ideal.mul_eq_inf_of_isCoprime
      ((Ideal.isCoprime_span_singleton_iff _ _).mpr h_coprime)

lemma span_prod_eq_iInf {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]
    [Fintype ι] (g : ι → R) (hc : Pairwise fun i j => IsCoprime (g i) (g j)) :
    Ideal.span ({∏ i, g i} : Set R) = ⨅ i, Ideal.span ({g i} : Set R) := by
  have h1 : ∏ i, g i = ∏ i ∈ Finset.univ, g i := by simp
  have h2 : (⨅ i, Ideal.span ({g i} : Set R)) =
      ⨅ i ∈ Finset.univ, Ideal.span ({g i} : Set R) := by simp
  rw [h1, h2]
  exact span_prod_eq_biInf Finset.univ g (fun i _ j _ hij => hc hij)

lemma isCoprime_of_irreducible_of_not_associated {K : Type*} [Field K]
    {p q : Polynomial K}
    (hp : Irreducible p) (hq : Irreducible q) (hne : ¬Associated p q) :
    IsCoprime p q := by
  have hp' : Prime p := UniqueFactorizationMonoid.irreducible_iff_prime.mp hp
  exact hp'.coprime_iff_not_dvd.mpr
    (fun h => hne (hp'.associated_of_dvd
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp hq) h))

lemma quotientInfRingEquivPiQuotient_algebraMap
    {K' : Type*} [Field K'] {ι : Type*} [DecidableEq ι] [Fintype ι]
    (I : ι → Ideal (Polynomial K'))
    (hc : Pairwise fun i j => IsCoprime (I i) (I j))
    (k : K') :
    (Ideal.quotientInfRingEquivPiQuotient I hc) ((algebraMap K' _) k) =
    (algebraMap K' _) k := by
  change (Ideal.quotientInfToPiQuotient I)
    ((Ideal.Quotient.mk _).comp C k) = _
  simp only [RingHom.comp_apply]
  unfold Ideal.quotientInfToPiQuotient
  simp only [Ideal.Quotient.lift_mk]
  ext i; rfl

end TensorSplitting
end

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ChowsLemma.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.ReesAlgebra
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.ValuativeCriterion
open Polynomial


noncomputable section

universe u v

/-- The coefficient of a finite sum of monomials indexed by a finset `s`: it equals
`g i` when `i ∈ s` and `0` otherwise. -/
lemma coeff_finset_sum_monomial {R : Type*} [CommRing R]
    {s : Finset ℕ} {g : ℕ → R} (i : ℕ) :
    (s.sum (fun j => Polynomial.monomial j (g j))).coeff i =
      if i ∈ s then g i else 0 := by
  change (Polynomial.lcoeff R i) (s.sum (fun j => Polynomial.monomial j (g j))) = _
  rw [map_sum]
  simp only [Polynomial.lcoeff_apply, Polynomial.coeff_monomial, Finset.sum_ite_eq']

namespace ChowBlowup

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- A polynomial in the Rees algebra of `I` maps under a ring homomorphism `f` into the
Rees algebra of the pushed-forward ideal `I.map f`. -/
theorem mem_reesAlgebra_map (f : R →+* S) (I : Ideal R)
    (p : R[X]) (hp : p ∈ reesAlgebra I) :
    Polynomial.map f p ∈ reesAlgebra (I.map f) := by
  rw [mem_reesAlgebra_iff] at hp ⊢
  intro i
  rw [Polynomial.coeff_map, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem f (hp i)

/-- If `s` lies in `(I.map e)^i` for a ring isomorphism `e`, then `e.symm s` lies in `I^i`. -/
lemma symm_mem_ideal_pow_of_mem_map_pow (e : R ≃+* S) (I : Ideal R)
    (i : ℕ) (s : S) (h : s ∈ (I.map (e : R →+* S)) ^ i) :
    e.symm s ∈ I ^ i := by
  rw [← Ideal.map_pow (e : R →+* S)] at h
  rw [Ideal.mem_map_iff_of_surjective (e : R →+* S) e.surjective] at h
  obtain ⟨r, hr, hrs⟩ := h
  have : e.symm s = r := by rw [← hrs]; simp
  rw [this]; exact hr

/-- Pulling back along the inverse of a ring isomorphism preserves membership in the Rees algebra. -/
theorem mem_reesAlgebra_map_symm (e : R ≃+* S) (I : Ideal R)
    (q : S[X]) (hq : q ∈ reesAlgebra (I.map (e : R →+* S))) :
    Polynomial.map (e.symm : S →+* R) q ∈ reesAlgebra I := by
  rw [mem_reesAlgebra_iff] at hq ⊢
  intro i
  rw [Polynomial.coeff_map]
  exact symm_mem_ideal_pow_of_mem_map_pow e I i _ (hq i)

end ChowBlowup
end

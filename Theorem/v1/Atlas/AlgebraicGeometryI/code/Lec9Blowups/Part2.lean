/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec9Blowups.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.ReesAlgebra
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Def.v1.Atlas.AlgebraicGeometryI.code.Lec9Blowups.Part2
open Polynomial


namespace Lec9Blowups

/-- If `φ : R → A` is surjective, the induced map on blowup algebras is
surjective. -/
theorem blowupMapRestrict_surjective {R A : Type*} [CommRing R] [CommRing A]
    (φ : R →+* A) (hφ : Function.Surjective φ) (𝔪 : Ideal A) :
    Function.Surjective (blowupMapRestrict φ 𝔪) := by
  intro ⟨g, hg⟩
  rw [mem_blowupAlgebra_iff] at hg
  classical

  have lift : ∀ i ∈ g.support, ∃ r ∈ (𝔪.comap φ) ^ i, φ r = g.coeff i := by
    intro i _
    have h2 : g.coeff i ∈ Ideal.map φ ((𝔪.comap φ) ^ i) := by
      rw [Ideal.map_pow, Ideal.map_comap_of_surjective φ hφ]
      exact hg i
    exact (Ideal.mem_map_iff_of_surjective φ hφ).mp h2
  choose r hr hrφ using lift

  set f := g.support.sum fun i =>
    monomial i (if hi : i ∈ g.support then r i hi else 0)
  have hf : f ∈ blowupAlgebra R (𝔪.comap φ) := by
    apply Subalgebra.sum_mem
    intro i hi
    simp only [hi, dite_true]
    exact blowupAlgebra.monomial_mem.mpr (hr i hi)
  refine ⟨⟨f, hf⟩, ?_⟩
  apply Subtype.ext
  show (Polynomial.map φ f) = g
  rw [Polynomial.map_sum]
  conv_rhs => rw [g.as_sum_support]
  apply Finset.sum_congr rfl
  intro i hi
  simp [hi, map_monomial, hrφ i hi]

end Lec9Blowups

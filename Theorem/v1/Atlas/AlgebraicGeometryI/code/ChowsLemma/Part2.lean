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
import Def.v1.Atlas.AlgebraicGeometryI.code.ChowsLemma
open Polynomial


noncomputable section

universe u v

namespace ChowBlowup

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- If `f : R →+* A` is surjective, the induced map of Rees algebras is also surjective. -/
theorem reesAlgebra_comap_to_rees_surjective {R A : Type*} [CommRing R] [CommRing A]
    (f : R →+* A) (hf : Function.Surjective f) (I : Ideal A) :
    Function.Surjective (reesAlgebra_comap_to_rees f I) := by
  intro ⟨q, hq⟩
  rw [mem_reesAlgebra_iff] at hq
  classical
  have hlift : ∀ i, ∃ r ∈ (I.comap f) ^ i, f r = q.coeff i := by
    intro i
    have hi := hq i
    rw [← Ideal.map_comap_of_surjective f hf I, ← Ideal.map_pow] at hi
    exact (Ideal.mem_map_iff_of_surjective f hf).mp hi
  choose g hg_mem hg_eq using hlift
  set p := q.support.sum (fun i => Polynomial.monomial i (g i)) with hp_def
  have hp : p ∈ reesAlgebra (I.comap f) := by
    rw [mem_reesAlgebra_iff]
    intro i
    rw [hp_def, coeff_finset_sum_monomial]
    split_ifs with hi
    · exact hg_mem i
    · exact ((I.comap f) ^ i).zero_mem
  refine ⟨⟨p, hp⟩, ?_⟩
  apply Subtype.ext
  show (Polynomial.map f p) = q
  ext i
  rw [coeff_map, hp_def, coeff_finset_sum_monomial]
  split_ifs with hi
  · exact hg_eq i
  · simp only [map_zero]
    have : q.coeff i = 0 := by rwa [Polynomial.mem_support_iff, not_not] at hi
    exact this.symm

end ChowBlowup
end

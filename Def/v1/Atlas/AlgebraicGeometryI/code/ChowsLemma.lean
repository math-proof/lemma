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
import Theorem.v1.Atlas.AlgebraicGeometryI.code.ChowsLemma
open Polynomial


noncomputable section

universe u v

namespace ChowBlowup

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- A ring isomorphism `e : R ≃+* S` induces a ring isomorphism between the Rees algebra of `I`
and the Rees algebra of `I.map e`. -/
def reesAlgebra_ringEquiv (e : R ≃+* S) (I : Ideal R) :
    reesAlgebra I ≃+* reesAlgebra (I.map (e : R →+* S)) where
  toFun p := ⟨Polynomial.map (e : R →+* S) p.1,
    mem_reesAlgebra_map _ I p.1 p.2⟩
  invFun q := ⟨Polynomial.map (e.symm : S →+* R) q.1,
    mem_reesAlgebra_map_symm e I q.1 q.2⟩
  left_inv p := by ext; simp [Polynomial.map_map]
  right_inv q := by ext; simp [Polynomial.map_map]
  map_mul' p q := Subtype.ext (Polynomial.map_mul (e : R →+* S))
  map_add' p q := Subtype.ext (Polynomial.map_add (e : R →+* S))

/-- The ring homomorphism from the Rees algebra of `I.comap f` to the Rees algebra of `I`,
induced coefficient-wise by `f`. -/
def reesAlgebra_comap_to_rees {R A : Type*} [CommRing R] [CommRing A]
    (f : R →+* A) (I : Ideal A) :
    reesAlgebra (I.comap f) →+* reesAlgebra I :=
  (Polynomial.mapRingHom f).restrict (reesAlgebra (I.comap f)) (reesAlgebra I)
    (fun p hp => by
      rw [mem_reesAlgebra_iff] at hp ⊢
      intro i; simp [coeff_map]; exact Ideal.le_comap_pow f i (hp i))

end ChowBlowup
end

import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Jacobson.Ring

universe u v

namespace IsAlgClosed

section FiniteType

variable {K : Type u} [Field K]

variable (K) in

noncomputable def pointOfMaximal [IsAlgClosed K] {A : Type v} [CommRing A]
    [Algebra K A] [Algebra.FiniteType K A] (m : Ideal A) [m.IsMaximal] : A →ₐ[K] K :=
  have algebraMap_quotient_bijective :
      Function.Bijective (algebraMap K (A ⧸ m)) := by
    letI : Field (A ⧸ m) := Ideal.Quotient.field m
    have : Module.Finite K (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ m)
    have : Algebra.IsIntegral K (A ⧸ m) := inferInstance
    exact IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e := RingEquiv.ofBijective (algebraMap K (A ⧸ m)) algebraMap_quotient_bijective
  { toRingHom := e.symm.toRingHom.comp (Ideal.Quotient.mk m)
    commutes' := fun k => by
      change e.symm (Ideal.Quotient.mk m (algebraMap K A k)) = k
      rw [Ideal.Quotient.mk_algebraMap]
      exact e.symm_apply_apply k }

end FiniteType

end IsAlgClosed

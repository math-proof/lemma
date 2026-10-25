-- Carved from Lemma/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean: instance decls only.
import Class.AlgebraicCurve_DivisorPushPull
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.Algebra.Polynomial.Lifts
import Lemma.AlgebraicCurve.PlacesOverDVR

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero IsLocalRing

namespace AlgebraicCurve

namespace Place


section Chart

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
variable (w : Place K F)

instance (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) :
    (center R w hw).IsPrime :=
  Ideal.comap_isPrime _ _

end Chart

variable {K F F' : Type*} [Field K] [Field F] [Field F']

section Setup

variable (v : Place K F)

instance : IsDedekindDomain (integralClosureAt F' v) :=
  integralClosure.isDedekindDomain v.toValuationSubring F F'

instance : IsFractionRing (integralClosureAt F' v) F' :=
  integralClosure.isFractionRing_of_finite_extension (A := v.toValuationSubring) F F'

instance : Module.Finite v.toValuationSubring (integralClosureAt F' v) :=
  IsIntegralClosure.finite v.toValuationSubring F F' _


instance : Module.IsTorsionFree v.toValuationSubring (integralClosureAt F' v) := by
  rw [Module.isTorsionFree_iff_smul_eq_zero]
  intro r c hrc
  rw [Algebra.smul_def] at hrc
  rcases mul_eq_zero.mp hrc with h | h
  · exact Or.inl (algebraMap_integralClosureAt_injective v (by rw [h, map_zero]))
  · exact Or.inr h

end Setup


end Place

end AlgebraicCurve

end

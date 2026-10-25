-- Carved from Lemma/Definitions/Def_GaloisRep_RatLocalizedAtResidue.lean: instance decls only.
import Mathlib
import Def.GaloisRep_Flat
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt

namespace GaloisRep

noncomputable section

instance ratLocalizedAt.span_isPrime (q : ℕ) [Fact q.Prime] : (Ideal.span {(q : ℤ)}).IsPrime := by
  have hq : Prime (q : ℤ) := by
    rw [Int.prime_iff_natAbs_prime]
    simpa using (Fact.out : q.Prime)
  exact (Ideal.span_singleton_prime hq.ne_zero).mpr hq


instance instAlgebraRatLocalizedAtZMod (q : ℕ) [Fact q.Prime] :
    Algebra ↥(ratLocalizedAt q) (ZMod q) :=
  (ratLocalizedAtResidue q).toAlgebra

example (q : ℕ) [Fact q.Prime] : Algebra ↥(ratLocalizedAt q) (AlgebraicClosure (ZMod q)) :=
  inferInstance
example (q : ℕ) [Fact q.Prime] :
    IsScalarTower ↥(ratLocalizedAt q) (ZMod q) (AlgebraicClosure (ZMod q)) :=
  inferInstance

end

end GaloisRep

-- Carved from Lemma/Definitions/Def_LanglandsTunnell_ArtinFrobenius.lean: instance decls only.
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.FieldTheory.Galois.IsGaloisGroup

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell.P2.Artin

open NumberField IsDedekindDomain
open Deep.NTSupply
open scoped nonZeroDivisors

section Frob

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

instance isGaloisGroup_ringOfIntegers [IsGalois K M] : IsGaloisGroup (M ≃ₐ[K] M) (𝓞 K) (𝓞 M) :=
  IsGaloisGroup.of_isFractionRing (M ≃ₐ[K] M) (𝓞 K) (𝓞 M) K M

omit [NumberField K] [NumberField M] in


instance primeAbove_isMaximal : (primeAbove K M v).IsMaximal := (exists_prime_over K M v).choose_spec.1

omit [NumberField M] in

instance primeAbove_liesOver : (primeAbove K M v).LiesOver v.asIdeal := ⟨(under_primeAbove K M v).symm⟩

omit [NumberField K] [NumberField M] in

instance primeAbove_finite : Finite (𝓞 M ⧸ primeAbove K M v) := Ideal.finiteQuotientOfFreeOfNeBot _ (primeAbove_ne_bot K M v)

omit [NumberField K] in

end Frob


#print axioms LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers
#print axioms LanglandsTunnell.P2.Artin.algebraMap_ringOfIntegers_injective
#print axioms LanglandsTunnell.P2.Artin.exists_prime_over
#print axioms LanglandsTunnell.P2.Artin.primeAbove
#print axioms LanglandsTunnell.P2.Artin.primeAbove_isMaximal
#print axioms LanglandsTunnell.P2.Artin.under_primeAbove
#print axioms LanglandsTunnell.P2.Artin.primeAbove_liesOver
#print axioms LanglandsTunnell.P2.Artin.ne_bot_of_under_eq
#print axioms LanglandsTunnell.P2.Artin.primeAbove_ne_bot
#print axioms LanglandsTunnell.P2.Artin.primeAbove_finite
#print axioms LanglandsTunnell.P2.Artin.finite_quotient_of_under_eq
#print axioms LanglandsTunnell.P2.Artin.artinFrob
#print axioms LanglandsTunnell.P2.Artin.isArithFrobAt_artinFrob
#print axioms LanglandsTunnell.P2.Artin.artinSymbol
#print axioms LanglandsTunnell.P2.Artin.artinSymbol_prime

end LanglandsTunnell.P2.Artin

end

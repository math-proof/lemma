import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.Tactic.LinearCombination

namespace IharaLemma

structure IdempotentSplitting (B : Type) [CommRing B] where
  n : ℕ
  e : Fin n → B
  𝔪 : Fin n → Ideal B
  coi : CompleteOrthogonalIdempotents e
  isMaximal : ∀ i, (𝔪 i).IsMaximal
  exists_eq : ∀ I : Ideal B, I.IsMaximal → ∃ i, 𝔪 i = I
  mem_iff : ∀ i j, e i ∈ 𝔪 j ↔ i ≠ j

namespace IdempotentSplitting

variable {B : Type} [CommRing B] (S : IdempotentSplitting B)


end IdempotentSplitting

section CornerModule

variable {B : Type} [CommRing B] {M : Type} [AddCommGroup M] [Module B M]


end CornerModule


namespace IdempotentSplitting

variable {B : Type} [CommRing B] (S : IdempotentSplitting B) (i : Fin S.n)


section Base

variable (𝒪 : Type) [CommRing 𝒪] [Algebra 𝒪 B]


end Base


section CornerModule

variable {M : Type} [AddCommGroup M] [Module B M]


end CornerModule

section Base

variable (𝒪 : Type) [CommRing 𝒪] [Algebra 𝒪 B]


end Base

section BaseModule

variable (𝒪 : Type) [CommRing 𝒪] [Algebra 𝒪 B]
variable {M : Type} [AddCommGroup M] [Module B M] [Module 𝒪 M] [IsScalarTower 𝒪 B M]


end BaseModule

end IdempotentSplitting

end IharaLemma

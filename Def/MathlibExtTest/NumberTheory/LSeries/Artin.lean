/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/LSeries/Artin.lean -/


import Def.NumberTheory.LSeries.Artin
import Lemma.Nat.LSeries.Artin


namespace RepresentationTest

open Representation

/-- Trivial local datum for the unit group: unramified with trivial
Frobenius, giving the standard Riemann-zeta local factor. -/
noncomputable def unitLocalDatum : ArtinLocalDatum Unit where
  decomposition := ⊤
  inertia := ⊥
  frobenius := 1

def primeTwo : Nat.Primes := ⟨2, Nat.prime_two⟩

end RepresentationTest

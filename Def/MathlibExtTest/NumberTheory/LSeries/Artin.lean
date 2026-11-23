/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/LSeries/Artin.lean -/

module

public import Def.NumberTheory.LSeries.Artin
public import Theorem.Nat.LSeries.Artin

@[expose] public section

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

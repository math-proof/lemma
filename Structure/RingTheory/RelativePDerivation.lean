/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/RelativePDerivation.lean -/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Def.RingTheory.RelativePDerivation
-- Relative p-derivation associated to a ring homomorphism.
-- Source: ZP-curves-inAV-new-new.tex lines 270-279,
-- def:p-derivation-relative-to-a-ring-homomorphism
-- p is prime (line 167), no characteristic assumption, rings are commutative.
-- C_p(X,Y) = (X^p+Y^p-(X+Y)^p)/p ∈ ℤ[X,Y].


public section

namespace MetaMathlibExt

-- Bundled relative p-derivation of u : A →+* B.
-- Exactly the three laws from the source definition.
structure RelativePDerivation (p : ℕ) [Fact p.Prime] {A B : Type*} [CommRing A] [CommRing B]
    (u : A →+* B) where
  toFun : A → B
  map_one : toFun 1 = 0
  map_add : ∀ x y : A, toFun (x + y) = toFun x + toFun y + pDerivationCorrection p (u x) (u y)
  map_mul : ∀ x y : A, toFun (x * y) =
    (u x) ^ p * toFun y + (u y) ^ p * toFun x + (p : B) * toFun x * toFun y

end MetaMathlibExt

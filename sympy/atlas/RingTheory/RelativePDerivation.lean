/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/RelativePDerivation.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Order.Interval.Finset.Nat

-- Relative p-derivation associated to a ring homomorphism.
-- Source: ZP-curves-inAV-new-new.tex lines 270-279,
-- def:p-derivation-relative-to-a-ring-homomorphism
-- p is prime (line 167), no characteristic assumption, rings are commutative.
-- C_p(X,Y) = (X^p+Y^p-(X+Y)^p)/p ∈ ℤ[X,Y].

namespace MetaMathlibExt

-- Integral coefficient -(choose p i)/p for 0 < i < p.
-- For p prime this is an integer; we represent it as integer division in ℤ
-- and cast to B, avoiding division in B.
def pDerivationCorrectionCoeff (p : ℕ) [Fact p.Prime] (i : ℕ) : ℤ :=
  -((Nat.choose p i : ℤ) / (p : ℤ))

-- C_p(x,y) = ∑_{1 ≤ i < p} (-(choose p i)/p) * x^i * y^{p-i}
-- This equals (x^p+y^p-(x+y)^p)/p as an element of B.
def pDerivationCorrection {B : Type*} [CommRing B] (p : ℕ) [Fact p.Prime] (x y : B) : B :=
  ∑ i ∈ Finset.Ico 1 p, ((pDerivationCorrectionCoeff p i : B) * x ^ i * y ^ (p - i))

-- Bundled relative p-derivation of u : A →+* B.
-- Exactly the three laws from the source definition.
structure RelativePDerivation (p : ℕ) [Fact p.Prime] {A B : Type*} [CommRing A] [CommRing B]
    (u : A →+* B) where
  toFun : A → B
  map_one : toFun 1 = 0
  map_add : ∀ x y : A, toFun (x + y) = toFun x + toFun y + pDerivationCorrection p (u x) (u y)
  map_mul : ∀ x y : A, toFun (x * y) =
    (u x) ^ p * toFun y + (u y) ^ p * toFun x + (p : B) * toFun x * toFun y

namespace RelativePDerivation

variable {p : ℕ} [Fact p.Prime] {A B : Type*} [CommRing A] [CommRing B] {u : A →+* B}

instance : CoeFun (RelativePDerivation p u) (fun _ => A → B) where
  coe d := d.toFun
end RelativePDerivation
end MetaMathlibExt

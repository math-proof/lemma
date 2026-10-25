/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/RelativePDerivation.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Order.Interval.Finset.Nat
import Structure.RingTheory.RelativePDerivation
-- Relative p-derivation associated to a ring homomorphism.
-- Source: ZP-curves-inAV-new-new.tex lines 270-279,
-- def:p-derivation-relative-to-a-ring-homomorphism
-- p is prime (line 167), no characteristic assumption, rings are commutative.
-- C_p(X,Y) = (X^p+Y^p-(X+Y)^p)/p ∈ ℤ[X,Y].


namespace MetaMathlibExt

namespace RelativePDerivation

variable {p : ℕ} [Fact p.Prime] {A B : Type*} [CommRing A] [CommRing B] {u : A →+* B}

instance : CoeFun (RelativePDerivation p u) (fun _ => A → B) where
  coe d := d.toFun

end RelativePDerivation
end MetaMathlibExt

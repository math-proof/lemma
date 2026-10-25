/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/ConductorIdeal.lean -/

import Mathlib.RingTheory.Conductor
import Mathlib.RingTheory.Finiteness.Subalgebra
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Noetherian.Basic
variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

/-!
# Conductor ideal of a subalgebra

For a subalgebra `A` of a commutative `R`-algebra `S`, the conductor ideal of `A`
is the largest ideal of `S` contained in `A`: it consists of those `s : S` with
`s * t ∈ A` for every `t : S`. For `A = Algebra.adjoin R {x}` this recovers
Mathlib's element-generated conductor `conductor R x`.
-/


namespace Subalgebra

/-- The conductor ideal of a subalgebra `A`: the largest ideal of `S`
contained in `A`. -/
def conductorIdeal (A : Subalgebra R S) : Ideal S where
  carrier := {s : S | ∀ t : S, s * t ∈ A}
  zero_mem' t := by simp
  add_mem' ha hb t := by simpa only [add_mul] using A.add_mem (ha t) (hb t)
  smul_mem' c a ha t := by
    simpa only [smul_eq_mul, mul_left_comm, mul_assoc] using ha (c * t)

end Subalgebra

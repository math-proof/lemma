/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Frobenius/Splitting.lean -/

import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.Frobenius

open scoped Pointwise

namespace Ideal

section SplitsCompletely

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {G : Type*} [Group G] [Finite G] [MulSemiringAction G B]
  [SMulCommClass G A B] [Algebra.IsInvariant A B G]
  {p : Ideal A} {P : Ideal B} [P.IsPrime] [P.LiesOver p]
end SplitsCompletely
end Ideal
section Conditional
end Conditional
section Unramified
end Unramified

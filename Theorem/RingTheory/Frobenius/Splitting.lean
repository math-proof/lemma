/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Frobenius/Splitting.lean -/
module

public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import Mathlib.RingTheory.Frobenius
open scoped Pointwise

public section

section SplitsCompletely

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {G : Type*} [Group G] [Finite G] [MulSemiringAction G B]
  [SMulCommClass G A B] [Algebra.IsInvariant A B G]
  {p : Ideal A} {P : Ideal B} [P.IsPrime] [P.LiesOver p]
end SplitsCompletely
namespace Ideal

end Ideal
section Conditional
end Conditional
section Unramified
end Unramified

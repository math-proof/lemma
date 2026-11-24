module
public import Theorem.NumberTheory.NumberField.RayClass.Modulus.Part5
public import Theorem.Nat.NumberField.RayClass.Modulus
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.ClassGroup.Basic
public import Theorem.NumberTheory.NumberField.RayClass.RayGroup


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/RayGroup.lean -/
@[expose] noncomputable section

open scoped nonZeroDivisors

/-!
# Ray groups attached to a modulus (N403 foundation)

Built over `NumberField.Modulus`, whose infinite-place multiplication
uses union, representing truncated exponent addition `min (m v + n v) 1`
(the ATLAS-extracted `max` formula was a typo).
-/


namespace NumberField

namespace Modulus

variable {K : Type*} [Field K] [NumberField K]

/-- Elements of `Kˣ` whose principal ideal is coprime to the modulus. -/
def rayElements (m : Modulus K) : Subgroup Kˣ :=
  Subgroup.comap (toPrincipalIdeal (𝓞 K) K)
    (coprimeFractionalIdeals m)

end Modulus
end NumberField

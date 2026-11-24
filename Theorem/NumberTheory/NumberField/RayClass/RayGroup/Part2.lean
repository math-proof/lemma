module
public import Theorem.NumberTheory.NumberField.RayClass.Modulus.Part5
public import Theorem.Nat.NumberField.RayClass.Modulus
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.ClassGroup.Basic
public import Def.NumberTheory.NumberField.RayClass.RayGroup.Part2


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

theorem mem_rayElements_iff (m : Modulus K) (x : Kˣ) :
    x ∈ rayElements m ↔
      toPrincipalIdeal (𝓞 K) K x ∈
        coprimeFractionalIdeals m :=
  Subgroup.mem_comap

end Modulus
end NumberField

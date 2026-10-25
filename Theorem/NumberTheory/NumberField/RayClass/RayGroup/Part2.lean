/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/RayGroup.lean -/

import Theorem.NumberTheory.NumberField.RayClass.Modulus.Part5
import Lemma.Nat.NumberField.RayClass.Modulus
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.ClassGroup.Basic
import Def.NumberTheory.NumberField.RayClass.RayGroup.Part2
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

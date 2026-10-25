/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Unramified.lean -/

import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Smooth.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.Instances
import Def.NumberTheory.NumberField.Unramified


namespace NumberField

namespace IsUnramifiedIn

/-- The contracted maximal prime is prime, as the comap of the maximal (hence
prime) ideal of the local factor. -/
theorem normalizedTensorCompositumPrime_isPrime
    (E F : IntermediateField ℚ L)
    (p : Ideal ℤ) [p.IsPrime] (h : Algebra.IsUnramifiedIn (𝓞 F) p)
    (Q : Ideal (𝓞 (E ⊔ F : IntermediateField ℚ L)))
    [Q.IsPrime] [Q.LiesOver p] :
    (normalizedTensorCompositumPrime E F p h Q).IsPrime := by
  unfold normalizedTensorCompositumPrime
  infer_instance

end IsUnramifiedIn
end NumberField

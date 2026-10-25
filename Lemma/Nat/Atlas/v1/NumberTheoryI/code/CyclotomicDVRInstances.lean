import Mathlib
import sympy.Basic
import Instance.v1.Atlas.NumberTheoryI.code.CyclotomicDVRInstances
open CyclotomicDVR
open scoped Padic


namespace CyclotomicDVR

/--
[isLocalRing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/CyclotomicDVRInstances.lean)
-/
@[path]
lemma isLocalRing
  {p : ℕ}
  [hp : Fact (Nat.Prime p)]
  {L : Type*}
  [Field L]
  [Algebra ℚ_[p] L]
  [IsCyclotomicExtension {p} ℚ_[p] L] :
-- imply
  IsLocalRing ↥(integralClosure ℤ_[p] L) :=
-- proof
  integral_closure_isLocalRing ℤ_[p] ℚ_[p] L
attribute [local instance] isLocalRing

end CyclotomicDVR

namespace CyclotomicDVR

/--
[isDVR](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/CyclotomicDVRInstances.lean)
-/
@[path]
lemma isDVR
  {p : ℕ}
  [hp : Fact (Nat.Prime p)]
  {L : Type*}
  [Field L]
  [Algebra ℚ_[p] L]
  [IsCyclotomicExtension {p} ℚ_[p] L] :
-- imply
  IsDiscreteValuationRing ↥(integralClosure ℤ_[p] L) :=
-- proof
  thm_9_22_integralClosure_isDVR ℤ_[p] ℚ_[p] L

end CyclotomicDVR

namespace CyclotomicDVR

/--
[isAdicComplete](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/CyclotomicDVRInstances.lean)
-/
@[path]
lemma isAdicComplete
  {p : ℕ}
  [hp : Fact (Nat.Prime p)]
  {L : Type*}
  [Field L]
  [Algebra ℚ_[p] L]
  [IsCyclotomicExtension {p} ℚ_[p] L] :
-- imply
  IsAdicComplete (IsLocalRing.maximalIdeal ↥(integralClosure ℤ_[p] L)) ↥(integralClosure ℤ_[p] L) :=
-- proof
  integral_closure_isAdicComplete ℤ_[p] ℚ_[p] L
end CyclotomicDVR



-- created on 2026-10-23

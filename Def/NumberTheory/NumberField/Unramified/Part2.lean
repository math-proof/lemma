/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Unramified.lean -/

import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Smooth.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.Instances
import Theorem.NumberTheory.NumberField.Unramified.Part2


namespace NumberField

namespace IsUnramifiedIn

attribute [instance] normalizedTensorCompositumPrime_isPrime

/-- Canonical localization map: the universal property of
`Localization.AtPrime` applied at the contracted maximal prime. An element
outside the contracted prime maps outside the maximal ideal of the local target
`T`, hence to a unit.

This is a plain `RingHom`, not an `AlgHom`: no `Algebra A S` or
`IsScalarTower A C S` data is installed, since that instance search is fragile.
No `IsLocalization` or `AlgEquiv` claim is made here: the missing
bijection/local-factor identification remains a later infrastructure problem,
and localization at `RingHom.ker g` is in general false. -/
noncomputable def normalizedTensorLocalizationToCompositumAtPrime
    (E F : IntermediateField ℚ L)
    (p : Ideal ℤ) [p.IsPrime] (h : Algebra.IsUnramifiedIn (𝓞 F) p)
    (Q : Ideal (𝓞 (E ⊔ F : IntermediateField ℚ L)))
    [Q.IsPrime] [Q.LiesOver p] :
    let qC := normalizedTensorCompositumPrime E F p h Q
    let S := Localization.AtPrime qC
    let T := Localization.AtPrime Q
    S →+* T := by
  have hprime : (normalizedTensorCompositumPrime E F p h Q).IsPrime :=
    normalizedTensorCompositumPrime_isPrime E F p h Q
  letI := hprime
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime Q) :=
    Localization.AtPrime.algebraOfLiesOver p Q
  exact IsLocalization.lift
    (M := (normalizedTensorCompositumPrime E F p h Q).primeCompl)
    (g := (normalizedTensorToCompositumAtPrime E F p h Q).toRingHom)
    (fun y => by
      have hy' : (normalizedTensorToCompositumAtPrime E F p h Q) y.val ∉
          IsLocalRing.maximalIdeal (Localization.AtPrime Q) := by
        intro hmem
        exact y.property (by
          unfold normalizedTensorCompositumPrime
          exact hmem)
      exact IsLocalRing.notMem_maximalIdeal.mp hy')

end IsUnramifiedIn
end NumberField

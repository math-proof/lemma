/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Unramified.lean -/

import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Smooth.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.Instances


namespace NumberField

variable {L : Type*} [Field L] [NumberField L]

/-- Semilocal étaleness above an unramified prime: localizing the whole finite
algebra `𝓞 K` at the prime-complement of `p` (inverting everything outside `p`,
keeping all local factors above `p` simultaneously) is étale over the local
base `Localization.AtPrime p`.

This packages the primewise unramified hypothesis used by
`isUnramifiedAtPrime_sup` in the primary Lean source for ATLAS `NumberTheoryI`
target N390, Proposition 19.14. It is the semilocal algebra, not a single local
factor `Localization.AtPrime Q`. -/
theorem IsUnramifiedIn.etale_localization {K : Type*} [Field K] [NumberField K]
    (p : Ideal ℤ) [p.IsPrime] (h : Algebra.IsUnramifiedIn (𝓞 K) p) :
    Algebra.Etale (Localization.AtPrime p)
      (Localization (Algebra.algebraMapSubmonoid (𝓞 K) p.primeCompl)) := by
  let S_p := Localization (Algebra.algebraMapSubmonoid (𝓞 K) p.primeCompl)
  have hFP : Algebra.FinitePresentation (Localization.AtPrime p) S_p :=
    (Algebra.FinitePresentation.of_finiteType (R := Localization.AtPrime p)
      (A := S_p)).mp inferInstance
  have hFU : Algebra.FormallyUnramified (Localization.AtPrime p) S_p := by
    rw [Algebra.formallyUnramified_iff_forall]
    intro x
    let q := x.asIdeal.under (𝓞 K)
    have hqprime : q.IsPrime := inferInstance
    have hmem : (⟨q, hqprime⟩ : PrimeSpectrum (𝓞 K)) ∈ Set.range
        (PrimeSpectrum.comap (algebraMap (𝓞 K) S_p)) := by
      refine ⟨x, ?_⟩
      apply PrimeSpectrum.ext
      change (x.asIdeal.under (𝓞 K)) = _
      rfl
    rw [PrimeSpectrum.localization_comap_range
      (Localization (Algebra.algebraMapSubmonoid (𝓞 K) p.primeCompl))
      (Algebra.algebraMapSubmonoid (𝓞 K) p.primeCompl)] at hmem
    have hle : q.under ℤ ≤ p := by
      apply Ideal.disjoint_map_primeCompl_iff_comap_le.mp
      exact Disjoint.symm hmem
    have hunram : Algebra.IsUnramifiedAt ℤ q := by
      by_cases hq0 : q = ⊥
      · simpa only [hq0] using
          (Algebra.isUnramifiedAt_bot (R := ℤ) (S := 𝓞 K))
      · have heq : p = q.under ℤ :=
          ((hqprime.under ℤ).isMaximal (q.under_ne_bot ℤ hq0) |>.eq_of_le
            (inferInstance : p.IsPrime).ne_top hle).symm
        have hlie : q.LiesOver p := ⟨heq⟩
        exact h q hqprime hlie
    let _ : Algebra.IsUnramifiedAt (𝓞 K) x.asIdeal :=
      Algebra.FormallyUnramified.of_isLocalization q.primeCompl
    let _ : Algebra.IsUnramifiedAt ℤ q := hunram
    have hlie2 : x.asIdeal.LiesOver q := ⟨rfl⟩
    let _ : x.asIdeal.LiesOver q := hlie2
    have hbase : Algebra.IsUnramifiedAt ℤ x.asIdeal :=
      Algebra.IsUnramifiedAt.comp q x.asIdeal
    let _ : Algebra.IsUnramifiedAt ℤ x.asIdeal := hbase
    exact Algebra.IsUnramifiedAt.of_restrictScalars ℤ x.asIdeal
  exact Algebra.Etale.of_formallyUnramified_of_flat

end NumberField

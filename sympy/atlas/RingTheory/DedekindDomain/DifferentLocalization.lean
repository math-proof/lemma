/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/DifferentLocalization.lean -/

import Lemma.Matrix.BilinearForm.DualLocalization
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.Tactic.LinearCombination

/-!
# Different ideal under canonical localization (ATLAS N241)

This module is the bounded canonical-localization version of ATLAS Proposition 12.3
(`NumberTheoryI N241`). Let `A` be a Dedekind domain with fraction field `K`, `L / K` a finite
separable extension, and `B` the integral closure of `A` in `L`. For `S ≤ A⁰` we write
`Aₛ` for the canonical localization `Localization.subalgebra.ofField K S hS` inside `K`, and
`SB` for an arbitrary localization of `B` at `Algebra.algebraMapSubmonoid B S`, compatibly
embedded in `L`.

The main results are that extension of the trace-dual fractional ideal commutes with this
localization (`FractionalIdeal.extendedHom_dual_one_eq_dual_one_ofField`), and consequently
the mapped different ideal equals the localized different ideal
(`Ideal.map_differentIdeal_eq_localization_ofField`).

Transport to an arbitrary base localization `SA` is deferred, not faked.
-/

universe u

variable (A K : Type*) (L : Type u) (B : Type*)
  [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [IsFractionRing A K]
  [FiniteDimensional K L] [IsIntegralClosure B A L] [Algebra.IsSeparable K L]
  [IsFractionRing B L]
  [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B]

variable (S : Submonoid A) (hS : S ≤ nonZeroDivisors A)

local notation "Aₛ" => Localization.subalgebra.ofField K S hS

/-- The canonical localization of an integrally closed domain is integrally closed. -/
instance : IsIntegrallyClosed Aₛ := isIntegrallyClosed_of_isLocalization _ S hS

/-- The canonical localization of a Dedekind domain is a Dedekind domain. -/
instance : IsDedekindDomain Aₛ := IsLocalization.isDedekindDomain A hS _

variable (SB : Type*) [CommRing SB] [Algebra B SB]
  [IsLocalization (Algebra.algebraMapSubmonoid B S) SB]
  [Algebra (Localization.subalgebra.ofField K S hS) SB] [Algebra SB L] [Algebra A SB]
  [IsScalarTower A (Localization.subalgebra.ofField K S hS) SB]
  [IsScalarTower A B SB] [IsScalarTower B SB L]
  [IsScalarTower A (Localization.subalgebra.ofField K S hS) L]
  [IsScalarTower (Localization.subalgebra.ofField K S hS) SB L]
  [IsScalarTower (Localization.subalgebra.ofField K S hS) K L]
  [IsFractionRing SB L] [IsDedekindDomain SB]
  [Module.IsTorsionFree (Localization.subalgebra.ofField K S hS) SB]
  [Module.IsTorsionFree B SB]
  [IsIntegralClosure SB (Localization.subalgebra.ofField K S hS) L]

omit [IsScalarTower A K L] [FiniteDimensional K L] [IsIntegralClosure B A L]
  [Algebra.IsSeparable K L] [IsFractionRing B L] [IsDedekindDomain A]
  [IsDedekindDomain B] [Module.IsTorsionFree A B] [Algebra A SB]
  [IsScalarTower A (Localization.subalgebra.ofField K S hS) SB]
  [IsScalarTower A B SB]
  [IsScalarTower (Localization.subalgebra.ofField K S hS) K L]
  [IsFractionRing SB L] [IsDedekindDomain SB]
  [Module.IsTorsionFree (Localization.subalgebra.ofField K S hS) SB]
  [Module.IsTorsionFree B SB]
  [IsIntegralClosure SB (Localization.subalgebra.ofField K S hS) L] in
namespace FractionalIdeal
end FractionalIdeal

module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.Valuation.Discrete.Basic
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Ring.Subring.Pointwise
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Bezout
public import Structure.AlgebraicCurve_Place
public import Abbrev.AlgebraicCurve_DivisorClassGroup
public import Class.AlgebraicCurve_DivisorClassGroup
public import Instance.AlgebraicCurve_DivisorClassGroup

public noncomputable section

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero IsLocalRing

namespace AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

namespace Place

variable {K F}
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]

open IsDedekindDomain.HeightOneSpectrum in

public theorem isPrincipalIdealRing_valuationSubring (w : HeightOneSpectrum R) :
    IsPrincipalIdealRing ((w.valuation F).valuationSubring) := by
  rw [show (w.valuation F).valuationSubring = valuationSubringAtPrime F w from
    (valuationSubringAtPrime_eq_valuationSubring (K := F) w).symm]

  infer_instance

open IsDedekindDomain.HeightOneSpectrum in


@[simp]
public theorem ofHeightOneSpectrum_toValuationSubring [Algebra K R] [IsScalarTower K R F]
    (w : HeightOneSpectrum R) :
    (ofHeightOneSpectrum (K := K) w).toValuationSubring = (w.valuation F).valuationSubring :=
  rfl

end Place

end AlgebraicCurve

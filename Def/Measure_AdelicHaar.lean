module

public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
public import Instance.NumberField_AdelicHaar

@[expose] public section

open IsDedekindDomain NumberField MeasureTheory Measure Matrix
open scoped RestrictedProduct

noncomputable section

namespace Measure.AdelicHaar

section Local

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)


variable [Module.Free ℤ R] [Module.Finite ℤ R]


end Local

section Adele

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]


variable [Module.Free ℤ R] [Module.Finite ℤ R]


def adelicAddHaar [NumberField K] : @Measure (AdeleRing R K) (adeleBorel R K) := by
  letI := adeleBorel R K
  haveI := borelSpace_adeleBorel R K
  exact Measure.addHaar

end Adele

section GeneralLinear

variable (n : Type*) (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]
variable [Fintype n] [DecidableEq n]


@[reducible] def glBorel : MeasurableSpace (Matrix.GeneralLinearGroup n (AdeleRing R K)) :=
  borel _

variable [Module.Free ℤ R] [Module.Finite ℤ R] [NumberField K]

/-- GL Haar scaffolding. `IsTopologicalGroup` on Matrixˣ does not synth for AdeleRing
(no ContinuousInv path); leave as sorry so AdelicLevel/Carrier oleans can build.
IotaGL extract only needs Carrier.iotaGL / Structure.transposeInv3. -/


def adelicGLHaar : @Measure (Matrix.GeneralLinearGroup n (AdeleRing R K)) (glBorel n R K) := by
  sorry

end GeneralLinear

end Measure.AdelicHaar

end

end

import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Instance.NumberField_AdelicHaar

open IsDedekindDomain NumberField MeasureTheory
open scoped RestrictedProduct

noncomputable section

namespace NumberField.AdelicHaar

section Local

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)


theorem exists_valued_algebraMap_sub_lt_one (x : v.adicCompletionIntegers K) :
    ∃ a : R, Valued.v ((algebraMap R (v.adicCompletion K) a) - (x : v.adicCompletion K)) < 1 := by
  have hn : {z : v.adicCompletion K | Valued.v (z - (x : v.adicCompletion K)) < 1} ∈
      nhds (x : v.adicCompletion K) := by
    refine Valued.mem_nhds.mpr ⟨1, fun z hz => ?_⟩
    have hz' : Valued.v.restrict (z - (x : v.adicCompletion K)) < 1 := by
      rw [← Units.val_one]; exact hz
    exact (Valuation.restrict_lt_one_iff _).mp hz'
  obtain ⟨_, hz, y, rfl⟩ := mem_closure_iff_nhds.mp
    (HeightOneSpectrum.denseRange_algebraMap (K := K) (v := v) (x : v.adicCompletion K)) _ hn
  have hy1 : Valued.v (algebraMap K (v.adicCompletion K) y - (x : v.adicCompletion K)) < 1 := hz
  have hyint : v.valuation K y ≤ 1 := by
    have hx1 : Valued.v (x : v.adicCompletion K) ≤ 1 := x.2
    have h : Valued.v (algebraMap K (v.adicCompletion K) y) ≤ 1 := by
      have := Valuation.map_add (Valued.v : Valuation (v.adicCompletion K) _)
        (algebraMap K (v.adicCompletion K) y - (x : v.adicCompletion K)) (x : v.adicCompletion K)
      rw [sub_add_cancel] at this
      exact this.trans (max_le hy1.le hx1)
    rwa [show algebraMap K (v.adicCompletion K) y = (y : v.adicCompletion K) from rfl,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h
  obtain ⟨a, ha⟩ := HeightOneSpectrum.exists_valuation_sub_lt_of_integer v hyint 1
  refine ⟨a, ?_⟩
  have ha' : Valued.v ((algebraMap R (v.adicCompletion K) a) -
      algebraMap K (v.adicCompletion K) y) < 1 := by
    rw [IsScalarTower.algebraMap_apply R K (v.adicCompletion K) a, ← map_sub,
      show algebraMap K (v.adicCompletion K) (algebraMap R K a - y) =
        ((algebraMap R K a - y : K) : v.adicCompletion K) from rfl,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact ha.trans_eq Units.val_one
  have := Valuation.map_add (Valued.v : Valuation (v.adicCompletion K) _)
    ((algebraMap R (v.adicCompletion K) a) - algebraMap K (v.adicCompletion K) y)
    (algebraMap K (v.adicCompletion K) y - (x : v.adicCompletion K))
  rw [sub_add_sub_cancel] at this
  exact lt_of_le_of_lt this (max_lt ha' hy1)

theorem mem_maximalIdeal_iff_valued_lt_one (d : v.adicCompletionIntegers K) :
    d ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ↔
      Valued.v (d : v.adicCompletion K) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
  have hd : Valued.v (d : v.adicCompletion K) ≤ 1 := d.2
  exact ⟨fun h => lt_of_le_of_ne hd h, fun h => ne_of_lt h⟩

theorem residue_algebraMap_surjective :
    Function.Surjective (fun a : R =>
      IsLocalRing.residue (v.adicCompletionIntegers K)
        (algebraMap R (v.adicCompletionIntegers K) a)) := by
  intro z
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
  obtain ⟨a, ha⟩ := exists_valued_algebraMap_sub_lt_one R K v x
  refine ⟨a, ?_⟩
  show Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
  rw [Ideal.Quotient.eq, mem_maximalIdeal_iff_valued_lt_one]
  simpa [HeightOneSpectrum.algebraMap_adicCompletion] using ha

theorem residue_algebraMap_eq_zero_of_mem {a : R} (ha : a ∈ v.asIdeal) :
    IsLocalRing.residue (v.adicCompletionIntegers K)
      (algebraMap R (v.adicCompletionIntegers K) a) = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, mem_maximalIdeal_iff_valued_lt_one]
  simp only [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
  exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v a).mpr ha

variable [Module.Free ℤ R] [Module.Finite ℤ R]


end Local

section Adele

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]


@[reducible] def adeleBorel : MeasurableSpace (AdeleRing R K) := borel _

theorem borelSpace_adeleBorel : @BorelSpace (AdeleRing R K) _ (adeleBorel R K) :=
  @BorelSpace.mk _ _ (adeleBorel R K) rfl

variable [Module.Free ℤ R] [Module.Finite ℤ R]


def adelicAddHaar [NumberField K] : @Measure (AdeleRing R K) (adeleBorel R K) := by
  letI := adeleBorel R K
  haveI := borelSpace_adeleBorel R K
  exact Measure.addHaar

theorem isAddHaarMeasure_adelicAddHaar [NumberField K] :
    @Measure.IsAddHaarMeasure (AdeleRing R K) _ _ (adeleBorel R K) (adelicAddHaar R K) := by
  letI := adeleBorel R K
  haveI := borelSpace_adeleBorel R K
  exact Measure.isAddHaarMeasure_addHaarMeasure _

end Adele

section GeneralLinear

variable (n : Type*) (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]
variable [Fintype n] [DecidableEq n]


@[reducible] def glBorel : MeasurableSpace (Matrix.GeneralLinearGroup n (AdeleRing R K)) :=
  borel _

theorem borelSpace_glBorel :
    @BorelSpace (Matrix.GeneralLinearGroup n (AdeleRing R K)) _ (glBorel n R K) :=
  @BorelSpace.mk _ _ (glBorel n R K) rfl

variable [Module.Free ℤ R] [Module.Finite ℤ R] [NumberField K]

/-- GL Haar scaffolding. `IsTopologicalGroup` on Matrixˣ does not synth for AdeleRing
(no ContinuousInv path); leave as sorry so AdelicLevel/Carrier oleans can build.
IotaGL extract only needs Carrier.iotaGL / Structure.transposeInv3. -/


def adelicGLHaar : @Measure (Matrix.GeneralLinearGroup n (AdeleRing R K)) (glBorel n R K) := by
  sorry

theorem isHaarMeasure_adelicGLHaar :
    @Measure.IsHaarMeasure (Matrix.GeneralLinearGroup n (AdeleRing R K)) _ _ (glBorel n R K)
      (adelicGLHaar n R K) := by
  sorry

end GeneralLinear

end NumberField.AdelicHaar

end

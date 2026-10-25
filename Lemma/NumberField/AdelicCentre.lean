import Instance.NumberField_AdelicHaar
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Abbrev.NumberField_AdelicCentre

open IsDedekindDomain NumberField MeasureTheory
open scoped Pointwise

noncomputable section

namespace NumberField.AdelicCentre

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem center_eq_range_scalar :
    Subgroup.center (GL (Fin 2) (AdeleRing R K))
      = (Matrix.GeneralLinearGroup.scalar (Fin 2) : (AdeleRing R K)ˣ →* _).range :=
  Matrix.GeneralLinearGroup.center_eq_range_scalar

theorem scalar_injective :
    Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin 2) : (AdeleRing R K)ˣ →* _) :=
  fun a b h => by
    have := congrArg (fun g : GL (Fin 2) (AdeleRing R K) => (g : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 0 0) h
    exact Units.ext (by simpa using this)

theorem measure_image_mk_pos {m : MeasurableSpace (AdelicPGL2 R K)} (μ : Measure (AdelicPGL2 R K))
    [μ.IsOpenPosMeasure] {D : Set (GL (Fin 2) (AdeleRing R K))}
    (h : ∃ U : Set (GL (Fin 2) (AdeleRing R K)), IsOpen U ∧ U.Nonempty ∧ U ⊆ D) :
    0 < μ ((QuotientGroup.mk : GL (Fin 2) (AdeleRing R K) → AdelicPGL2 R K) '' D) := by
  obtain ⟨U, hU, hne, hsub⟩ := h
  exact ((QuotientGroup.isOpenMap_coe U hU).measure_pos μ (hne.image _)).trans_le
    (measure_mono (Set.image_mono hsub))

theorem measure_image_mk_lt_top {m : MeasurableSpace (AdelicPGL2 R K)} (μ : Measure (AdelicPGL2 R K))
    [IsFiniteMeasureOnCompacts μ] {C : Set (GL (Fin 2) (AdeleRing R K))} (hC : IsCompact C) :
    μ ((QuotientGroup.mk : GL (Fin 2) (AdeleRing R K) → AdelicPGL2 R K) '' C) < ⊤ :=
  (hC.image QuotientGroup.continuous_mk).measure_lt_top

theorem image_mk_subset_of_subset_mul_center {D C : Set (GL (Fin 2) (AdeleRing R K))}
    (h : D ⊆ C * ((Subgroup.center (GL (Fin 2) (AdeleRing R K)) : Set (GL (Fin 2) (AdeleRing R K))))) :
    (QuotientGroup.mk : _ → AdelicPGL2 R K) '' D ⊆ (QuotientGroup.mk : _ → AdelicPGL2 R K) '' C := by
  rintro _ ⟨d, hd, rfl⟩
  obtain ⟨c, hc, z, hz, rfl⟩ := h hd
  refine ⟨c, hc, ?_⟩
  rw [QuotientGroup.eq]
  simpa using hz

@[reducible] def pglBorel : MeasurableSpace (AdelicPGL2 R K) := borel _

theorem borelSpace_pglBorel : @BorelSpace (AdelicPGL2 R K) _ (pglBorel R K) :=
  @BorelSpace.mk _ _ (pglBorel R K) rfl

section NumberFieldCase

variable [Module.Free ℤ R] [Module.Finite ℤ R] [NumberField K]


def adelicPGLHaar : @Measure (AdelicPGL2 R K) (pglBorel R K) := by
  letI := pglBorel R K
  haveI := borelSpace_pglBorel R K
  exact Measure.haar

theorem isHaarMeasure_adelicPGLHaar :
    @Measure.IsHaarMeasure (AdelicPGL2 R K) _ _ (pglBorel R K) (adelicPGLHaar R K) := by
  letI := pglBorel R K
  haveI := borelSpace_pglBorel R K
  exact Measure.isHaarMeasure_haarMeasure _

theorem adelicPGLHaar_image_pos {D : Set (GL (Fin 2) (AdeleRing R K))}
    (h : ∃ U : Set (GL (Fin 2) (AdeleRing R K)), IsOpen U ∧ U.Nonempty ∧ U ⊆ D) :
    0 < adelicPGLHaar R K ((QuotientGroup.mk : _ → AdelicPGL2 R K) '' D) := by
  letI := pglBorel R K
  haveI := borelSpace_pglBorel R K
  haveI := isHaarMeasure_adelicPGLHaar R K
  exact measure_image_mk_pos R K _ h

theorem adelicPGLHaar_image_lt_top_of_subset {D C : Set (GL (Fin 2) (AdeleRing R K))} (hC : IsCompact C)
    (h : D ⊆ C * ((Subgroup.center (GL (Fin 2) (AdeleRing R K)) : Set (GL (Fin 2) (AdeleRing R K))))) :
    adelicPGLHaar R K ((QuotientGroup.mk : _ → AdelicPGL2 R K) '' D) < ⊤ := by
  letI := pglBorel R K
  haveI := borelSpace_pglBorel R K
  haveI := isHaarMeasure_adelicPGLHaar R K
  exact lt_of_le_of_lt (measure_mono (image_mk_subset_of_subset_mul_center R K h))
    (measure_image_mk_lt_top R K _ hC)

end NumberFieldCase

end NumberField.AdelicCentre

end

-- Carved from Lemma/Definitions/Def_AutomorphicForm_HyperbolicMeasure.lean: instance decls only.
import Mathlib

open MeasureTheory Set
open scoped MatrixGroups Pointwise NNReal ENNReal

noncomputable section

namespace FLT.HyperbolicMeasure

open UpperHalfPlane

example : MeasureSpace ℍ := inferInstance

example : SigmaFinite (volume : Measure ℍ) := inferInstance

example : SMulInvariantMeasure (GL (Fin 2) ℝ) ℍ volume := inferInstance

example : IsFiniteMeasureOnCompacts (volume : Measure ℍ) := inferInstance


instance : SMulInvariantMeasure SL(2, ℤ) ℍ (volume : Measure ℍ) where
  measure_preimage_smul g s hs := by

    simp only [MulAction.compHom_smul_def]
    exact SMulInvariantMeasure.measure_preimage_smul (Matrix.SpecialLinearGroup.mapGL ℝ g) hs


instance : Measure.IsOpenPosMeasure (volume : Measure ℍ) := by
  constructor
  intro U hU hUne

  rw [UpperHalfPlane.volume_eq_lintegral]

  have himage_open : IsOpen (UpperHalfPlane.coe '' U) :=
    UpperHalfPlane.isOpenEmbedding_coe.isOpenMap U hU
  have himage_ne : (UpperHalfPlane.coe '' U).Nonempty := hUne.image _
  have hpos : 0 < volume (UpperHalfPlane.coe '' U) :=
    himage_open.measure_pos volume himage_ne

  refine ((MeasureTheory.setLIntegral_pos_iff measurable_density).mpr ?_).ne'
  refine hpos.trans_le (measure_mono fun w hw => ?_)
  exact ⟨density_ne_zero (Set.image_subset_range _ _ hw), hw⟩


end FLT.HyperbolicMeasure
end

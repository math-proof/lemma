-- Carved from Lemma/Definitions/Def_AutomorphicForm_AdelicMaximalCompact.lean: instance decls only.
import Instance.NumberField_AdelicHaar

set_option autoImplicit false

open NumberField NumberField.AdelicLevel MeasureTheory IsDedekindDomain
open AutomorphicForm.WindowedSiegel

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace AutomorphicForm

variable (K : Type*) [Field K] [NumberField K]


instance compactSpace_adelicMaximalCompact : CompactSpace (adelicMaximalCompact K) :=
  isCompact_iff_compactSpace.mp (isCompact_adelicMaximalCompact K)


instance isHaarMeasure_maximalCompactHaar : (maximalCompactHaar K).IsHaarMeasure := by
  rw [maximalCompactHaar]; infer_instance

instance isProbabilityMeasure_maximalCompactHaar : IsProbabilityMeasure (maximalCompactHaar K) :=
  ⟨by rw [maximalCompactHaar, ← TopologicalSpace.PositiveCompacts.coe_top]; exact Measure.haarMeasure_self⟩


section Factors

variable (S : Finset (HeightOneSpectrum (𝓞 K)))


instance compactSpace_maximalCompactAt : CompactSpace (maximalCompactAt K S) :=
  isCompact_iff_compactSpace.mp (isCompact_maximalCompactAt K S)

instance compactSpace_maximalCompactAway : CompactSpace (maximalCompactAway K S) :=
  isCompact_iff_compactSpace.mp (isCompact_maximalCompactAway K S)


instance isHaarMeasure_maximalCompactAtHaar : (maximalCompactAtHaar K S).IsHaarMeasure := by
  rw [maximalCompactAtHaar]; infer_instance

instance isProbabilityMeasure_maximalCompactAtHaar : IsProbabilityMeasure (maximalCompactAtHaar K S) :=
  ⟨by rw [maximalCompactAtHaar, ← TopologicalSpace.PositiveCompacts.coe_top]; exact Measure.haarMeasure_self⟩

instance isHaarMeasure_maximalCompactAwayHaar : (maximalCompactAwayHaar K S).IsHaarMeasure := by
  rw [maximalCompactAwayHaar]; infer_instance

instance isProbabilityMeasure_maximalCompactAwayHaar :
    IsProbabilityMeasure (maximalCompactAwayHaar K S) :=
  ⟨by rw [maximalCompactAwayHaar, ← TopologicalSpace.PositiveCompacts.coe_top]; exact Measure.haarMeasure_self⟩

end Factors

end AutomorphicForm

end

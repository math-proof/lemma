import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Exact3D.FiniteCurrentScaleClockBridge
open StatMech StatMech.Exact3D StatMech.Exact3D.FreePositiveSubcriticalMassAnnulusScaleClockAverageErrorNearCritical StatMech.Exact3D.FreePositiveSubcriticalMassAnnulusScaleClockTerminalAverageErrorNearCritical StatMech.Exact3D.FreePositiveSubcriticalMassAnnulusScaleClockTerminalErrorNearCritical StatMech.Exact3D.FreePositiveSubcriticalMassAnnulusScaleClockBoundedTerminalErrorNearCritical StatMech.Exact3D.FreePositiveSubcriticalMassCriticalDistanceClockComparisonNearCritical StatMech.Exact3D.FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalErrorNearCritical StatMech.Exact3D.FreePositiveSubcriticalMassCriticalDistanceClockComparisonBoundedTerminalErrorNearCritical StatMech.Exact3D.FreePositiveSubcriticalMassCriticalDistanceClockComparisonAverageErrorNearCritical StatMech.Exact3D.FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalAverageErrorNearCritical StatMech.Exact3D.FiniteCurrentMassBridgeInputs StatMech.Exact3D.FiniteCurrentActualScheduleProjectionInputs


/--
[clockError_negligible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean)
-/
@[path]
private lemma clockError_negligible_eq
  {C : RGCertificate Ising3DModel}
  {hmass : FreePositiveSubcriticalMassBridge}
-- given
  (h : FreePositiveSubcriticalMassAnnulusScaleClockAverageErrorNearCritical C hmass) :
-- imply
  Filter.Tendsto (fun β : ℝ => (h.clock β - criticalDistanceScaleClock Ising3DModel h.relevantEigenvalue β) / (-Real.log (Ising.betaC 3 - β))) (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0) := by
-- proof
  apply StatMech.Exact3D.FreePositiveSubcriticalMassAnnulusScaleClockAverageErrorNearCritical.clockError_negligible h

/--
[accumulatedError_negligible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean)
-/
@[path]
private lemma accumulatedError_negligible_eq
  {C : RGCertificate Ising3DModel}
  {hmass : FreePositiveSubcriticalMassBridge}
-- given
  (h : FreePositiveSubcriticalMassAnnulusScaleClockAverageErrorNearCritical C hmass) :
-- imply
  Filter.Tendsto (fun β : ℝ => h.accumulatedError β / Real.log (Ising.betaC 3 - β)) (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0) := by
-- proof
  apply StatMech.Exact3D.FreePositiveSubcriticalMassAnnulusScaleClockAverageErrorNearCritical.accumulatedError_negligible h

/--
[clockError_negligible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean)
-/
@[path]
private lemma clockError_negligible_eq_2
  {C : RGCertificate Ising3DModel}
  {hmass : FreePositiveSubcriticalMassBridge}
-- given
  (h : FreePositiveSubcriticalMassAnnulusScaleClockTerminalAverageErrorNearCritical C hmass) :
-- imply
  Filter.Tendsto (fun β : ℝ => (h.clock β - criticalDistanceScaleClock Ising3DModel h.relevantEigenvalue β) / (-Real.log (Ising.betaC 3 - β))) (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0) := by
-- proof
  apply StatMech.Exact3D.FreePositiveSubcriticalMassAnnulusScaleClockTerminalAverageErrorNearCritical.clockError_negligible h

/--
[accumulatedError_negligible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean)
-/
@[path]
private lemma accumulatedError_negligible_eq_2
  {C : RGCertificate Ising3DModel}
  {hmass : FreePositiveSubcriticalMassBridge}
-- given
  (h : FreePositiveSubcriticalMassAnnulusScaleClockTerminalAverageErrorNearCritical C hmass) :
-- imply
  Filter.Tendsto (fun β : ℝ => h.accumulatedError β / Real.log (Ising.betaC 3 - β)) (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0) := by
-- proof
  apply StatMech.Exact3D.FreePositiveSubcriticalMassAnnulusScaleClockTerminalAverageErrorNearCritical.accumulatedError_negligible h

/--
[clockError_negligible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean)
-/
@[path]
private lemma clockError_negligible_eq_3
  {C : RGCertificate Ising3DModel}
  {hmass : FreePositiveSubcriticalMassBridge}
-- given
  (h : FreePositiveSubcriticalMassAnnulusScaleClockTerminalErrorNearCritical C hmass) :
-- imply
  Filter.Tendsto (fun β : ℝ => (h.clock β - criticalDistanceScaleClock Ising3DModel h.relevantEigenvalue β) / (-Real.log (Ising.betaC 3 - β))) (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0) := by
-- proof
  apply StatMech.Exact3D.FreePositiveSubcriticalMassAnnulusScaleClockTerminalErrorNearCritical.clockError_negligible h

/--
[averageAccumulatedError_negligible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean)
-/
@[path]
private lemma averageAccumulatedError_negligible_eq
  {C : RGCertificate Ising3DModel}
  {hmass : FreePositiveSubcriticalMassBridge}
-- given
  (h : FreePositiveSubcriticalMassAnnulusScaleClockTerminalErrorNearCritical C hmass) :
-- imply
  Filter.Tendsto (fun β : ℝ => h.accumulatedError β / h.clock β) (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0) := by
-- proof
  apply StatMech.Exact3D.FreePositiveSubcriticalMassAnnulusScaleClockTerminalErrorNearCritical.averageAccumulatedError_negligible h

/--
[clockError_negligible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean)
-/
@[path]
private lemma clockError_negligible_eq_4
  {C : RGCertificate Ising3DModel}
  {hmass : FreePositiveSubcriticalMassBridge}
-- given
  (h : FreePositiveSubcriticalMassAnnulusScaleClockBoundedTerminalErrorNearCritical C hmass) :
-- imply
  Filter.Tendsto (fun β : ℝ => (h.clock β - criticalDistanceScaleClock Ising3DModel h.relevantEigenvalue β) / (-Real.log (Ising.betaC 3 - β))) (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0) := by
-- proof
  apply StatMech.Exact3D.FreePositiveSubcriticalMassAnnulusScaleClockBoundedTerminalErrorNearCritical.clockError_negligible h

/--
[averageAccumulatedError_negligible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean)
-/
@[path]
private lemma averageAccumulatedError_negligible_eq_2
  {C : RGCertificate Ising3DModel}
  {hmass : FreePositiveSubcriticalMassBridge}
-- given
  (h : FreePositiveSubcriticalMassAnnulusScaleClockBoundedTerminalErrorNearCritical C hmass) :
-- imply
  Filter.Tendsto (fun β : ℝ => h.accumulatedError β / h.clock β) (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0) := by
-- proof
  apply StatMech.Exact3D.FreePositiveSubcriticalMassAnnulusScaleClockBoundedTerminalErrorNearCritical.averageAccumulatedError_negligible h

/--
[clock_ratio_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean)
-/
@[path]
private lemma clock_ratio_tendsto_eq
  {C : RGCertificate Ising3DModel}
  {hmass : FreePositiveSubcriticalMassBridge}
-- given
  (h : FreePositiveSubcriticalMassCriticalDistanceClockComparisonNearCritical C hmass) :
-- imply
  Filter.Tendsto (fun β : ℝ => h.clock β / (-Real.log (Ising.betaC 3 - β))) (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds ((Real.log h.relevantEigenvalue)⁻¹)) := by
-- proof
  apply StatMech.Exact3D.FreePositiveSubcriticalMassCriticalDistanceClockComparisonNearCritical.clock_ratio_tendsto h

/--
[averageAccumulatedError_negligible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean)
-/
@[path]
private lemma averageAccumulatedError_negligible_eq_3
  {C : RGCertificate Ising3DModel}
  {hmass : FreePositiveSubcriticalMassBridge}
-- given
  (h : FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalErrorNearCritical C hmass) :
-- imply
  Filter.Tendsto (fun β : ℝ => h.accumulatedError β / h.clock β) (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0) := by
-- proof
  apply StatMech.Exact3D.FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalErrorNearCritical.averageAccumulatedError_negligible h

/--
[averageAccumulatedError_negligible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean)
-/
@[path]
private lemma averageAccumulatedError_negligible_eq_4
  {C : RGCertificate Ising3DModel}
  {hmass : FreePositiveSubcriticalMassBridge}
-- given
  (h : FreePositiveSubcriticalMassCriticalDistanceClockComparisonBoundedTerminalErrorNearCritical C hmass) :
-- imply
  Filter.Tendsto (fun β : ℝ => h.accumulatedError β / h.clock β) (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0) := by
-- proof
  apply StatMech.Exact3D.FreePositiveSubcriticalMassCriticalDistanceClockComparisonBoundedTerminalErrorNearCritical.averageAccumulatedError_negligible h

/--
[accumulatedError_negligible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean)
-/
@[path]
private lemma accumulatedError_negligible_eq_3
  {C : RGCertificate Ising3DModel}
  {hmass : FreePositiveSubcriticalMassBridge}
-- given
  (h : FreePositiveSubcriticalMassCriticalDistanceClockComparisonAverageErrorNearCritical C hmass) :
-- imply
  Filter.Tendsto (fun β : ℝ => h.accumulatedError β / Real.log (Ising.betaC 3 - β)) (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0) := by
-- proof
  apply StatMech.Exact3D.FreePositiveSubcriticalMassCriticalDistanceClockComparisonAverageErrorNearCritical.accumulatedError_negligible h

/--
[accumulatedError_negligible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean)
-/
@[path]
private lemma accumulatedError_negligible_eq_4
  {C : RGCertificate Ising3DModel}
  {hmass : FreePositiveSubcriticalMassBridge}
-- given
  (h : FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalAverageErrorNearCritical C hmass) :
-- imply
  Filter.Tendsto (fun β : ℝ => h.accumulatedError β / Real.log (Ising.betaC 3 - β)) (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0) := by
-- proof
  apply StatMech.Exact3D.FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalAverageErrorNearCritical.accumulatedError_negligible h

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_scaleClock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_scaleClock_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hclock : FreePositiveSubcriticalMassScaleClockNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_scaleClock I C hagree hclock

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_annulusScaleClock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_annulusScaleClock_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hann : FreePositiveSubcriticalMassAnnulusScaleClockNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_annulusScaleClock I C hagree hann

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_annulusScaleClockAverageError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_annulusScaleClockAverageError_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (havg : FreePositiveSubcriticalMassAnnulusScaleClockAverageErrorNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_annulusScaleClockAverageError I C hagree havg

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_annulusScaleClockTerminalAverageError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_annulusScaleClockTerminalAverageError_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (havg : FreePositiveSubcriticalMassAnnulusScaleClockTerminalAverageErrorNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_annulusScaleClockTerminalAverageError I C hagree havg

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_annulusScaleClockTerminalError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_annulusScaleClockTerminalError_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hterm : FreePositiveSubcriticalMassAnnulusScaleClockTerminalErrorNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_annulusScaleClockTerminalError I C hagree hterm

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_annulusScaleClockBoundedTerminalError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_annulusScaleClockBoundedTerminalError_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hterm : FreePositiveSubcriticalMassAnnulusScaleClockBoundedTerminalErrorNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_annulusScaleClockBoundedTerminalError I C hagree hterm

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_criticalDistanceScaleClock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_criticalDistanceScaleClock_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hcal : FreePositiveSubcriticalMassCriticalDistanceScaleClockNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_criticalDistanceScaleClock I C hagree hcal

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_criticalDistanceClockComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_criticalDistanceClockComparison_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hcmp : FreePositiveSubcriticalMassCriticalDistanceClockComparisonNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_criticalDistanceClockComparison I C hagree hcmp

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_criticalDistanceClockComparisonTerminalError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_criticalDistanceClockComparisonTerminalError_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hterm : FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalErrorNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_criticalDistanceClockComparisonTerminalError I C hagree hterm

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_criticalDistanceClockComparisonTerminalAverageError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_criticalDistanceClockComparisonTerminalAverageError_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (havg : FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalAverageErrorNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_criticalDistanceClockComparisonTerminalAverageError I C hagree havg

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_criticalDistanceClockComparisonBoundedTerminalError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_criticalDistanceClockComparisonBoundedTerminalError_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hterm : FreePositiveSubcriticalMassCriticalDistanceClockComparisonBoundedTerminalErrorNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_criticalDistanceClockComparisonBoundedTerminalError I C hagree hterm

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_criticalDistanceClockComparisonAverageError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_criticalDistanceClockComparisonAverageError_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (havg : FreePositiveSubcriticalMassCriticalDistanceClockComparisonAverageErrorNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_criticalDistanceClockComparisonAverageError I C hagree havg

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_scaleClock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_scaleClock_eq_2
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hclock : FreePositiveSubcriticalMassScaleClockNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentActualScheduleProjectionInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_scaleClock I C hagree hclock

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_annulusScaleClock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_annulusScaleClock_eq_2
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hann : FreePositiveSubcriticalMassAnnulusScaleClockNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentActualScheduleProjectionInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_annulusScaleClock I C hagree hann

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_annulusScaleClockAverageError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_annulusScaleClockAverageError_eq_2
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (havg : FreePositiveSubcriticalMassAnnulusScaleClockAverageErrorNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentActualScheduleProjectionInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_annulusScaleClockAverageError I C hagree havg

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_annulusScaleClockTerminalAverageError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_annulusScaleClockTerminalAverageError_eq_2
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (havg : FreePositiveSubcriticalMassAnnulusScaleClockTerminalAverageErrorNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentActualScheduleProjectionInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_annulusScaleClockTerminalAverageError I C hagree havg

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_annulusScaleClockTerminalError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_annulusScaleClockTerminalError_eq_2
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hterm : FreePositiveSubcriticalMassAnnulusScaleClockTerminalErrorNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentActualScheduleProjectionInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_annulusScaleClockTerminalError I C hagree hterm

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_annulusScaleClockBoundedTerminalError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_annulusScaleClockBoundedTerminalError_eq_2
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hterm : FreePositiveSubcriticalMassAnnulusScaleClockBoundedTerminalErrorNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentActualScheduleProjectionInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_annulusScaleClockBoundedTerminalError I C hagree hterm

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_criticalDistanceScaleClock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_criticalDistanceScaleClock_eq_2
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hcal : FreePositiveSubcriticalMassCriticalDistanceScaleClockNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentActualScheduleProjectionInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_criticalDistanceScaleClock I C hagree hcal

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_criticalDistanceClockComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_criticalDistanceClockComparison_eq_2
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hcmp : FreePositiveSubcriticalMassCriticalDistanceClockComparisonNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentActualScheduleProjectionInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_criticalDistanceClockComparison I C hagree hcmp

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_criticalDistanceClockComparisonTerminalError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_criticalDistanceClockComparisonTerminalError_eq_2
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hterm : FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalErrorNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentActualScheduleProjectionInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_criticalDistanceClockComparisonTerminalError I C hagree hterm

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_criticalDistanceClockComparisonTerminalAverageError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_criticalDistanceClockComparisonTerminalAverageError_eq_2
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (havg : FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalAverageErrorNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentActualScheduleProjectionInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_criticalDistanceClockComparisonTerminalAverageError I C hagree havg

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_criticalDistanceClockComparisonBoundedTerminalError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_criticalDistanceClockComparisonBoundedTerminalError_eq_2
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hterm : FreePositiveSubcriticalMassCriticalDistanceClockComparisonBoundedTerminalErrorNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentActualScheduleProjectionInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_criticalDistanceClockComparisonBoundedTerminalError I C hagree hterm

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_criticalDistanceClockComparisonAverageError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_criticalDistanceClockComparisonAverageError_eq_2
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (havg : FreePositiveSubcriticalMassCriticalDistanceClockComparisonAverageErrorNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentActualScheduleProjectionInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_criticalDistanceClockComparisonAverageError I C hagree havg

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_scaleClock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_scaleClock_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hclock : FreePositiveSubcriticalMassScaleClockNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_scaleClock C hagree hlim hfixed hone hboundary hcmp hprojection hclock

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_annulusScaleClock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_annulusScaleClock_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hann : FreePositiveSubcriticalMassAnnulusScaleClockNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_annulusScaleClock C hagree hlim hfixed hone hboundary hcmp hprojection hann

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_annulusScaleClockAverageError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_annulusScaleClockAverageError_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (havg : FreePositiveSubcriticalMassAnnulusScaleClockAverageErrorNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_annulusScaleClockAverageError C hagree hlim hfixed hone hboundary hcmp hprojection havg

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_annulusScaleClockTerminalAverageError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_annulusScaleClockTerminalAverageError_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (havg : FreePositiveSubcriticalMassAnnulusScaleClockTerminalAverageErrorNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_annulusScaleClockTerminalAverageError C hagree hlim hfixed hone hboundary hcmp hprojection havg

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_annulusScaleClockTerminalError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_annulusScaleClockTerminalError_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hterm : FreePositiveSubcriticalMassAnnulusScaleClockTerminalErrorNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_annulusScaleClockTerminalError C hagree hlim hfixed hone hboundary hcmp hprojection hterm

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_annulusScaleClockBoundedTerminalError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_annulusScaleClockBoundedTerminalError_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hterm : FreePositiveSubcriticalMassAnnulusScaleClockBoundedTerminalErrorNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_annulusScaleClockBoundedTerminalError C hagree hlim hfixed hone hboundary hcmp hprojection hterm

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_criticalDistanceScaleClock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_criticalDistanceScaleClock_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hcal : FreePositiveSubcriticalMassCriticalDistanceScaleClockNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_criticalDistanceScaleClock C hagree hlim hfixed hone hboundary hcmp hprojection hcal

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_criticalDistanceClockComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_criticalDistanceClockComparison_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hclock : FreePositiveSubcriticalMassCriticalDistanceClockComparisonNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_criticalDistanceClockComparison C hagree hlim hfixed hone hboundary hcmp hprojection hclock

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_criticalDistanceClockComparisonTerminalError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_criticalDistanceClockComparisonTerminalError_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hterm : FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalErrorNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_criticalDistanceClockComparisonTerminalError C hagree hlim hfixed hone hboundary hcmp hprojection hterm

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_criticalDistanceClockComparisonTerminalAverageError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_criticalDistanceClockComparisonTerminalAverageError_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (havg : FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalAverageErrorNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_criticalDistanceClockComparisonTerminalAverageError C hagree hlim hfixed hone hboundary hcmp hprojection havg

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_criticalDistanceClockComparisonBoundedTerminalError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_criticalDistanceClockComparisonBoundedTerminalError_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hterm : FreePositiveSubcriticalMassCriticalDistanceClockComparisonBoundedTerminalErrorNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_criticalDistanceClockComparisonBoundedTerminalError C hagree hlim hfixed hone hboundary hcmp hprojection hterm

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_criticalDistanceClockComparisonAverageError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_criticalDistanceClockComparisonAverageError_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (havg : FreePositiveSubcriticalMassCriticalDistanceClockComparisonAverageErrorNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_criticalDistanceClockComparisonAverageError C hagree hlim hfixed hone hboundary hcmp hprojection havg


-- created on 2026-10-23

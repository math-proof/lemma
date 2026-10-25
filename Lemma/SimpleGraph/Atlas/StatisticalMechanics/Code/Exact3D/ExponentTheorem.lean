import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.ExponentTheorem
open StatMech StatMech.Exact3D


/--
[hasCriticalNu_eq_log_scale_div_log_thermal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma hasCriticalNu_eq_log_scale_div_log_thermal_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (hC : C.Valid correlationLength) :
-- imply
  HasCriticalNu M correlationLength (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.hasCriticalNu_eq_log_scale_div_log_thermal C correlationLength hC

/--
[hasCriticalNu_from_rgToExponentBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma hasCriticalNu_from_rgToExponentBridge_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (hbridge : C.RGToExponentBridge correlationLength) :
-- imply
  HasCriticalNu M correlationLength (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.hasCriticalNu_from_rgToExponentBridge C correlationLength hbridge

/--
[placeholder_hasCriticalNu_exact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma placeholder_hasCriticalNu_exact_eq
  {C : RGCertificate PlaceholderModel}
  {correlationLength : ℝ → ℝ}
-- given
  (hC : C.Valid correlationLength) :
-- imply
  HasCriticalNu PlaceholderModel correlationLength (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.placeholder_hasCriticalNu_exact C correlationLength hC

/--
[ising3D_hasCriticalNu_exact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_exact_eq
  {C : RGCertificate Ising3DModel}
  {correlationLength : ℝ → ℝ}
-- given
  (hC : C.Valid correlationLength) :
-- imply
  HasCriticalNu Ising3DModel correlationLength (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_hasCriticalNu_exact C correlationLength hC

/--
[hasCriticalNu_from_analyticBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma hasCriticalNu_from_analyticBridgeInputs_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {T : RGCertificate.AnalyticBridgeInputs C correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge} :
-- imply
  HasCriticalNu M correlationLength (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.hasCriticalNu_from_analyticBridgeInputs C correlationLength T

/--
[hasCriticalNu_from_analyticBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma hasCriticalNu_from_analyticBridgeInputs_congr_predictedExponent_eq
  {M : CriticalModel ι}
  {C D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {T : RGCertificate.AnalyticBridgeInputs C correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  HasCriticalNu M correlationLength (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.hasCriticalNu_from_analyticBridgeInputs_congr_predictedExponent correlationLength hpred T

/--
[hasCriticalNu_from_analyticPrefactorBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma hasCriticalNu_from_analyticPrefactorBridgeInputs_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength prefactor : ℝ → ℝ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {T : RGCertificate.AnalyticPrefactorBridgeInputs C correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge} :
-- imply
  HasCriticalNu M correlationLength (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.hasCriticalNu_from_analyticPrefactorBridgeInputs C correlationLength prefactor T

/--
[hasCriticalNu_from_analyticPrefactorBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma hasCriticalNu_from_analyticPrefactorBridgeInputs_congr_predictedExponent_eq
  {M : CriticalModel ι}
  {C D : RGCertificate M}
  {correlationLength prefactor : ℝ → ℝ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {T : RGCertificate.AnalyticPrefactorBridgeInputs C correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  HasCriticalNu M correlationLength (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.hasCriticalNu_from_analyticPrefactorBridgeInputs_congr_predictedExponent correlationLength prefactor hpred T

/--
[hasCriticalNu_from_analyticMassBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma hasCriticalNu_from_analyticMassBridgeInputs_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength mass massPrefactor : ℝ → ℝ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {T : RGCertificate.AnalyticMassBridgeInputs C correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge} :
-- imply
  HasCriticalNu M correlationLength (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.hasCriticalNu_from_analyticMassBridgeInputs C correlationLength mass massPrefactor T

/--
[hasCriticalNu_from_analyticMassBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma hasCriticalNu_from_analyticMassBridgeInputs_congr_predictedExponent_eq
  {M : CriticalModel ι}
  {C D : RGCertificate M}
  {correlationLength mass massPrefactor : ℝ → ℝ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {T : RGCertificate.AnalyticMassBridgeInputs C correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  HasCriticalNu M correlationLength (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.hasCriticalNu_from_analyticMassBridgeInputs_congr_predictedExponent correlationLength mass massPrefactor hpred T

/--
[ising3D_hasCriticalNu_from_isingAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_isingAnalyticTarget_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingAnalyticRGToExponentTarget C} :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_hasCriticalNu_from_isingAnalyticTarget C T

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_isingAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_isingAnalyticTarget_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingAnalyticRGToExponentTarget C} :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_isingAnalyticTarget C T

/--
[ising3D_hasCriticalNu_from_isingMassAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_isingMassAnalyticTarget_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingMassAnalyticRGToExponentTarget C} :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_hasCriticalNu_from_isingMassAnalyticTarget C T

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_isingMassAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_isingMassAnalyticTarget_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingMassAnalyticRGToExponentTarget C} :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_isingMassAnalyticTarget C T

/--
[ising3D_hasCriticalNu_from_isingMassPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_isingMassPowerLawTarget_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget C} :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_hasCriticalNu_from_isingMassPowerLawTarget C T

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_isingMassPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_isingMassPowerLawTarget_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget C} :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_isingMassPowerLawTarget C T

/--
[ising3D_hasCriticalNu_from_freeAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_freeAnalyticTarget_eq
  {C : RGCertificate Ising3DModel}
  {T : FreeAnalyticRGToPlusExponentTarget C} :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_hasCriticalNu_from_freeAnalyticTarget C T

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_freeAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_freeAnalyticTarget_eq
  {C : RGCertificate Ising3DModel}
  {T : FreeAnalyticRGToPlusExponentTarget C} :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_freeAnalyticTarget C T

/--
[ising3D_hasCriticalNu_from_freeMassAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_freeMassAnalyticTarget_eq
  {C : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget C} :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_hasCriticalNu_from_freeMassAnalyticTarget C T

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassAnalyticTarget_eq
  {C : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget C} :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassAnalyticTarget C T

/--
[ising3D_hasCriticalNu_from_freeMassPowerLawToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_freeMassPowerLawToPlusTarget_eq
  {C : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C} :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_hasCriticalNu_from_freeMassPowerLawToPlusTarget C T

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget_eq
  {C : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C} :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget C T

/--
[ising3D_hasCriticalNu_from_isingAnalyticTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_isingAnalyticTarget_congr_predictedExponent_eq
  {C D : RGCertificate Ising3DModel}
  {T : IsingAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_hasCriticalNu_from_isingAnalyticTarget_congr_predictedExponent hpred T

/--
[ising3D_hasCriticalNu_from_isingMassAnalyticTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_isingMassAnalyticTarget_congr_predictedExponent_eq
  {C D : RGCertificate Ising3DModel}
  {T : IsingMassAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_hasCriticalNu_from_isingMassAnalyticTarget_congr_predictedExponent hpred T

/--
[ising3D_hasCriticalNu_from_isingMassPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_isingMassPowerLawTarget_congr_predictedExponent_eq
  {C D : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_hasCriticalNu_from_isingMassPowerLawTarget_congr_predictedExponent hpred T

/--
[ising3D_hasCriticalNu_from_freeAnalyticTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_freeAnalyticTarget_congr_predictedExponent_eq
  {C D : RGCertificate Ising3DModel}
  {T : FreeAnalyticRGToPlusExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_hasCriticalNu_from_freeAnalyticTarget_congr_predictedExponent hpred T

/--
[ising3D_hasCriticalNu_from_freeMassAnalyticTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_freeMassAnalyticTarget_congr_predictedExponent_eq
  {C D : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_hasCriticalNu_from_freeMassAnalyticTarget_congr_predictedExponent hpred T

/--
[ising3D_hasCriticalNu_from_freeMassPowerLawToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_freeMassPowerLawToPlusTarget_congr_predictedExponent_eq
  {C D : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_hasCriticalNu_from_freeMassPowerLawToPlusTarget_congr_predictedExponent hpred T

/--
[ising3D_liminf_from_isingAnalyticTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_liminf_from_isingAnalyticTarget_congr_predictedExponent_eq
  {C D : RGCertificate Ising3DModel}
  {T : IsingAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminf_from_isingAnalyticTarget_congr_predictedExponent hpred T

/--
[ising3D_liminf_from_isingMassAnalyticTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_liminf_from_isingMassAnalyticTarget_congr_predictedExponent_eq
  {C D : RGCertificate Ising3DModel}
  {T : IsingMassAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminf_from_isingMassAnalyticTarget_congr_predictedExponent hpred T

/--
[ising3D_liminf_from_isingMassPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_liminf_from_isingMassPowerLawTarget_congr_predictedExponent_eq
  {C D : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminf_from_isingMassPowerLawTarget_congr_predictedExponent hpred T

/--
[ising3D_liminf_from_freeAnalyticTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_liminf_from_freeAnalyticTarget_congr_predictedExponent_eq
  {C D : RGCertificate Ising3DModel}
  {T : FreeAnalyticRGToPlusExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminf_from_freeAnalyticTarget_congr_predictedExponent hpred T

/--
[ising3D_liminf_from_freeMassAnalyticTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_liminf_from_freeMassAnalyticTarget_congr_predictedExponent_eq
  {C D : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminf_from_freeMassAnalyticTarget_congr_predictedExponent hpred T

/--
[ising3D_liminf_from_freeMassPowerLawToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_liminf_from_freeMassPowerLawToPlusTarget_congr_predictedExponent_eq
  {C D : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminf_from_freeMassPowerLawToPlusTarget_congr_predictedExponent hpred T

/--
[ising3D_hasCriticalNu_from_coordinateBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_coordinateBridge_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs C} :
-- imply
  HasCriticalNu Ising3DModel T.scaffold.correlationLength (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_hasCriticalNu_from_coordinateBridge C T

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_coordinateBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_coordinateBridge_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs C} :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_coordinateBridge C T

/--
[ising3D_hasCriticalNu_from_massCoordinateBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_massCoordinateBridge_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C} :
-- imply
  HasCriticalNu Ising3DModel T.scaffold.correlationLength (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_hasCriticalNu_from_massCoordinateBridge C T

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_massCoordinateBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_massCoordinateBridge_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C} :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_massCoordinateBridge C T

/--
[ising3D_hasCriticalNu_from_coordinateBridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_coordinateBridge_congr_predictedExponent_eq
  {C D : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.scaffold.correlationLength (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_hasCriticalNu_from_coordinateBridge_congr_predictedExponent hpred T

/--
[ising3D_hasCriticalNu_from_massCoordinateBridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_massCoordinateBridge_congr_predictedExponent_eq
  {C D : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.scaffold.correlationLength (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_hasCriticalNu_from_massCoordinateBridge_congr_predictedExponent hpred T

/--
[ising3D_liminf_from_coordinateBridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_liminf_from_coordinateBridge_congr_predictedExponent_eq
  {C D : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminf_from_coordinateBridge_congr_predictedExponent hpred T

/--
[ising3D_liminf_from_massCoordinateBridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_liminf_from_massCoordinateBridge_congr_predictedExponent_eq
  {C D : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminf_from_massCoordinateBridge_congr_predictedExponent hpred T

/--
[ising3D_hasCriticalNu_from_fkTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_fkTarget_eq
  {C : RGCertificate Ising3DModel}
  {T : FKToIsingAnalyticRGToExponentTarget C} :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_hasCriticalNu_from_fkTarget C T

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_fkTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_fkTarget_eq
  {C : RGCertificate Ising3DModel}
  {T : FKToIsingAnalyticRGToExponentTarget C} :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_fkTarget C T

/--
[ising3D_hasCriticalNu_from_fk_pOfBeta_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_fk_pOfBeta_eventually_eq_eq
  {C : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength C.predictedExponent)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_hasCriticalNu_from_fk_pOfBeta_eventually_eq C hfk hEq

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_fk_pOfBeta_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_fk_pOfBeta_eventually_eq_eq
  {C : RGCertificate Ising3DModel}
  {fkCorrelationLength : ℝ → ℝ}
-- given
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength C.predictedExponent)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_fk_pOfBeta_eventually_eq C hfk hEq

/--
[ising3D_hasCriticalNu_from_fk_pOfBeta_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_fk_pOfBeta_eventually_eq_congr_predictedExponent_eq
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength D.predictedExponent)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_hasCriticalNu_from_fk_pOfBeta_eventually_eq_congr_predictedExponent C hpred hfk hEq

/--
[ising3D_liminf_from_fk_pOfBeta_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_liminf_from_fk_pOfBeta_eventually_eq_congr_predictedExponent_eq
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {fkCorrelationLength : ℝ → ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength D.predictedExponent)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminf_from_fk_pOfBeta_eventually_eq_congr_predictedExponent C hpred hfk hEq

/--
[ising3D_hasCriticalNu_from_fk_pOfBeta_rgToExponentBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_fk_pOfBeta_rgToExponentBridge_eq
  {C : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (hfk : (C.retarget (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge fkCorrelationLength)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_hasCriticalNu_from_fk_pOfBeta_rgToExponentBridge C hfk hEq

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_fk_pOfBeta_rgToExponentBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_fk_pOfBeta_rgToExponentBridge_eq
  {C : RGCertificate Ising3DModel}
  {fkCorrelationLength : ℝ → ℝ}
-- given
  (hfk : (C.retarget (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge fkCorrelationLength)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_fk_pOfBeta_rgToExponentBridge C hfk hEq

/--
[ising3D_rgToExponentBridge_from_fk_pOfBeta_rgToExponentBridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_rgToExponentBridge_from_fk_pOfBeta_rgToExponentBridge_congr_predictedExponent_eq
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hfk : (D.retarget (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge fkCorrelationLength)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  C.RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.ising3D_rgToExponentBridge_from_fk_pOfBeta_rgToExponentBridge_congr_predictedExponent C hpred hfk hEq

/--
[ising3D_hasCriticalNu_from_fk_pOfBeta_rgToExponentBridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_fk_pOfBeta_rgToExponentBridge_congr_predictedExponent_eq
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hfk : (D.retarget (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge fkCorrelationLength)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_hasCriticalNu_from_fk_pOfBeta_rgToExponentBridge_congr_predictedExponent C hpred hfk hEq

/--
[ising3D_liminf_from_fk_pOfBeta_rgToExponentBridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_liminf_from_fk_pOfBeta_rgToExponentBridge_congr_predictedExponent_eq
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {fkCorrelationLength : ℝ → ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hfk : (D.retarget (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge fkCorrelationLength)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminf_from_fk_pOfBeta_rgToExponentBridge_congr_predictedExponent C hpred hfk hEq

/--
[ising3D_hasCriticalNu_from_fk_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_fk_exact_power_variable_prefactor_on_Ioo_eq
  {C : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pδ : ℝ}
-- given
  (hpδ : 0 < pδ)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-C.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_hasCriticalNu_from_fk_exact_power_variable_prefactor_on_Ioo C isingCorrelationLength fkCorrelationLength fkPrefactor pδ hpδ hpref_pos hlogpref hscaling hEq

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_fk_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_fk_exact_power_variable_prefactor_on_Ioo_eq
  {C : RGCertificate Ising3DModel}
  {fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pδ : ℝ}
-- given
  (hpδ : 0 < pδ)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-C.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_fk_exact_power_variable_prefactor_on_Ioo C fkCorrelationLength fkPrefactor pδ hpδ hpref_pos hlogpref hscaling hEq

/--
[ising3D_hasCriticalNu_from_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pδ : ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hpδ : 0 < pδ)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_hasCriticalNu_from_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent C isingCorrelationLength fkCorrelationLength fkPrefactor hpred pδ hpδ hpref_pos hlogpref hscaling hEq

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pδ : ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hpδ : 0 < pδ)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent C fkCorrelationLength fkPrefactor hpred pδ hpδ hpref_pos hlogpref hscaling hEq

/--
[ising3D_hasCriticalNu_from_fk_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_fk_exact_mass_power_variable_prefactor_on_Ioo_eq
  {C : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pδ : ℝ}
-- given
  (hpδ : 0 < pδ)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp (C.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_hasCriticalNu_from_fk_exact_mass_power_variable_prefactor_on_Ioo C isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor pδ hpδ hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_fk_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_fk_exact_mass_power_variable_prefactor_on_Ioo_eq
  {C : RGCertificate Ising3DModel}
  {fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pδ : ℝ}
-- given
  (hpδ : 0 < pδ)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp (C.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_fk_exact_mass_power_variable_prefactor_on_Ioo C fkCorrelationLength fkMass fkMassPrefactor pδ hpδ hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq

/--
[ising3D_hasCriticalNu_from_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pδ : ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hpδ : 0 < pδ)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp (D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_hasCriticalNu_from_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent C isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor hpred pδ hpδ hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pδ : ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hpδ : 0 < pδ)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp (D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent C fkCorrelationLength fkMass fkMassPrefactor hpred pδ hpδ hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq

/--
[ising3D_hasCriticalNu_from_fkPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_fkPowerLawTarget_eq
  {C : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_hasCriticalNu_from_fkPowerLawTarget C T

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_fkPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_fkPowerLawTarget_eq
  {C : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_fkPowerLawTarget C T

/--
[ising3D_hasCriticalNu_from_fkMassTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_fkMassTarget_eq
  {C : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget C} :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_hasCriticalNu_from_fkMassTarget C T

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_fkMassTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_fkMassTarget_eq
  {C : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget C} :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_fkMassTarget C T

/--
[ising3D_hasCriticalNu_from_fkMassPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_fkMassPowerLawTarget_eq
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_hasCriticalNu_from_fkMassPowerLawTarget C T

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_fkMassPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_fkMassPowerLawTarget_eq
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_fkMassPowerLawTarget C T

/--
[ising3D_hasCriticalNu_from_fkTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_fkTarget_congr_predictedExponent_eq
  {C D : RGCertificate Ising3DModel}
  {T : FKToIsingAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_hasCriticalNu_from_fkTarget_congr_predictedExponent hpred T

/--
[ising3D_hasCriticalNu_from_fkPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_fkPowerLawTarget_congr_predictedExponent_eq
  {C D : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_hasCriticalNu_from_fkPowerLawTarget_congr_predictedExponent hpred T

/--
[ising3D_hasCriticalNu_from_fkMassTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_fkMassTarget_congr_predictedExponent_eq
  {C D : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_hasCriticalNu_from_fkMassTarget_congr_predictedExponent hpred T

/--
[ising3D_hasCriticalNu_from_fkMassPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_fkMassPowerLawTarget_congr_predictedExponent_eq
  {C D : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_hasCriticalNu_from_fkMassPowerLawTarget_congr_predictedExponent hpred T

/--
[ising3D_liminf_from_fkTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_liminf_from_fkTarget_congr_predictedExponent_eq
  {C D : RGCertificate Ising3DModel}
  {T : FKToIsingAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminf_from_fkTarget_congr_predictedExponent hpred T

/--
[ising3D_liminf_from_fkPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_liminf_from_fkPowerLawTarget_congr_predictedExponent_eq
  {C D : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminf_from_fkPowerLawTarget_congr_predictedExponent hpred T

/--
[ising3D_liminf_from_fkMassTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_liminf_from_fkMassTarget_congr_predictedExponent_eq
  {C D : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminf_from_fkMassTarget_congr_predictedExponent hpred T

/--
[ising3D_liminf_from_fkMassPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentTheorem.lean)
-/
@[path]
private lemma ising3D_liminf_from_fkMassPowerLawTarget_congr_predictedExponent_eq
  {C D : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminf_from_fkMassPowerLawTarget_congr_predictedExponent hpred T


-- created on 2026-10-23

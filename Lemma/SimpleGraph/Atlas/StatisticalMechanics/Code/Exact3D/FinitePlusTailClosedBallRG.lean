import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBallRG.Part5
open StatMech StatMech.Exact3D StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate StatMech.Exact3D.FinitePlusTailClosedBallRGPackage


/--
[rgMap_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma rgMap_map_eq
  {n : ℕ}
  {α : Type}
  {C : FinitePlusTailClosedBallContractionCertificate n α}
  {scale : BlockScale} :
-- imply
  (C.rgMap scale).map = C.contraction.map := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.rgMap_map C scale

/--
[rgMap_scale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma rgMap_scale_eq
  {n : ℕ}
  {α : Type}
  {C : FinitePlusTailClosedBallContractionCertificate n α}
  {scale : BlockScale} :
-- imply
  (C.rgMap scale).scale = scale := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.rgMap_scale C scale

/--
[certificate_thermalEigenvalue_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma certificate_thermalEigenvalue_eq_eq
  {n : ℕ}
  {α : Type}
  {C : FinitePlusTailClosedBallContractionCertificate n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {thermal : ℝ}
-- given
  (hthermal : 1 < thermal) :
-- imply
  (C.certificate scale M thermal hthermal).thermalEigenvalue = thermal := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.certificate_thermalEigenvalue_eq C scale M thermal hthermal

/--
[certificate_scale_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma certificate_scale_eq_eq
  {n : ℕ}
  {α : Type}
  {C : FinitePlusTailClosedBallContractionCertificate n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {thermal : ℝ}
-- given
  (hthermal : 1 < thermal) :
-- imply
  (C.certificate scale M thermal hthermal).scale = scale := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.certificate_scale_eq C scale M thermal hthermal

/--
[certificate_fixedPoint_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma certificate_fixedPoint_eq_eq
  {n : ℕ}
  {α : Type}
  {C : FinitePlusTailClosedBallContractionCertificate n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {thermal : ℝ}
-- given
  (hthermal : 1 < thermal) :
-- imply
  (C.certificate scale M thermal hthermal).fixedPointData.fixedPoint = C.fixedPoint := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.certificate_fixedPoint_eq C scale M thermal hthermal

/--
[certificate_R_map_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma certificate_R_map_eq_eq
  {n : ℕ}
  {α : Type}
  {C : FinitePlusTailClosedBallContractionCertificate n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {thermal : ℝ}
-- given
  (hthermal : 1 < thermal) :
-- imply
  (C.certificate scale M thermal hthermal).R.map = C.contraction.map := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.certificate_R_map_eq C scale M thermal hthermal

/--
[certificate_predictedExponent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma certificate_predictedExponent_eq_eq
  {n : ℕ}
  {α : Type}
  {C : FinitePlusTailClosedBallContractionCertificate n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {thermal : ℝ}
-- given
  (hthermal : 1 < thermal) :
-- imply
  (C.certificate scale M thermal hthermal).predictedExponent = predictedNu scale thermal := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.certificate_predictedExponent_eq C scale M thermal hthermal

/--
[certificate_fixedPointEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma certificate_fixedPointEnclosure_eq
  {n : ℕ}
  {α : Type}
  {C : FinitePlusTailClosedBallContractionCertificate n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {thermal : ℝ}
-- given
  (hthermal : 1 < thermal) :
-- imply
  (C.certificate scale M thermal hthermal).FixedPointEnclosure := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.certificate_fixedPointEnclosure C scale M thermal hthermal

/--
[certificate_finiteCaseChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma certificate_finiteCaseChecks_eq
  {n : ℕ}
  {α : Type}
  {C : FinitePlusTailClosedBallContractionCertificate n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {thermal : ℝ}
-- given
  (hthermal : 1 < thermal) :
-- imply
  (C.certificate scale M thermal hthermal).FiniteCaseChecks := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.certificate_finiteCaseChecks C scale M thermal hthermal

/--
[certificate_tailBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma certificate_tailBounds_eq
  {n : ℕ}
  {α : Type}
  {C : FinitePlusTailClosedBallContractionCertificate n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {thermal : ℝ}
-- given
  (hthermal : 1 < thermal) :
-- imply
  (C.certificate scale M thermal hthermal).TailBounds := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.certificate_tailBounds C scale M thermal hthermal

/--
[certificate_linearizationEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma certificate_linearizationEnclosure_eq
  {n : ℕ}
  {α : Type}
  {C : FinitePlusTailClosedBallContractionCertificate n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {thermal : ℝ}
-- given
  (hthermal : 1 < thermal) :
-- imply
  (C.certificate scale M thermal hthermal).LinearizationEnclosure := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.certificate_linearizationEnclosure C scale M thermal hthermal

/--
[certificate_hyperbolicSplitting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma certificate_hyperbolicSplitting_eq
  {n : ℕ}
  {α : Type}
  {C : FinitePlusTailClosedBallContractionCertificate n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {thermal : ℝ}
-- given
  (hthermal : 1 < thermal) :
-- imply
  (C.certificate scale M thermal hthermal).HyperbolicSplitting := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.certificate_hyperbolicSplitting C scale M thermal hthermal

/--
[certificate_orbitEntry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma certificate_orbitEntry_eq
  {n : ℕ}
  {α : Type}
  {C : FinitePlusTailClosedBallContractionCertificate n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {thermal : ℝ}
-- given
  (hthermal : 1 < thermal) :
-- imply
  (C.certificate scale M thermal hthermal).OrbitEntry := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.certificate_orbitEntry C scale M thermal hthermal

/--
[certificate_fixedPoint_mem_closedBall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma certificate_fixedPoint_mem_closedBall_eq
  {n : ℕ}
  {α : Type}
  {C : FinitePlusTailClosedBallContractionCertificate n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {thermal : ℝ}
-- given
  (hthermal : 1 < thermal) :
-- imply
  FinitePlusTailState.ClosedBall C.center C.radius (C.certificate scale M thermal hthermal).fixedPointData.fixedPoint := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.certificate_fixedPoint_mem_closedBall C scale M thermal hthermal

/--
[rgMap_iterate_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma rgMap_iterate_eq_eq
  {n : ℕ}
  {α : Type}
  {C : FinitePlusTailClosedBallContractionCertificate n α}
  {scale : BlockScale}
  {k : ℕ}
  {x : FinitePlusTailState n α} :
-- imply
  ((C.rgMap scale).map^[k]) x = C.contraction.iterate k x := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.rgMap_iterate_eq C scale k x

/--
[rgMap_iterate_mem_closedBall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma rgMap_iterate_mem_closedBall_eq
  {n : ℕ}
  {α : Type}
  {C : FinitePlusTailClosedBallContractionCertificate n α}
  {scale : BlockScale}
  {x : FinitePlusTailState n α}
  {k : ℕ}
-- given
  (hx : FinitePlusTailState.ClosedBall C.center C.radius x) :
-- imply
  FinitePlusTailState.ClosedBall C.center C.radius (((C.rgMap scale).map^[k]) x) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.rgMap_iterate_mem_closedBall C scale hx k

/--
[certificate_iterate_mem_closedBall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma certificate_iterate_mem_closedBall_eq
  {n : ℕ}
  {α : Type}
  {C : FinitePlusTailClosedBallContractionCertificate n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {thermal : ℝ}
  {x : (C.certificate scale M thermal hthermal).H.carrier}
  {k : ℕ}
-- given
  (hthermal : 1 < thermal)
  (hx : FinitePlusTailState.ClosedBall C.center C.radius x) :
-- imply
  FinitePlusTailState.ClosedBall C.center C.radius ((((C.certificate scale M thermal hthermal).R.map)^[k]) x) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.certificate_iterate_mem_closedBall C scale M thermal hthermal hx k

/--
[certificate_valid_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma certificate_valid_of_bridge_eq
  {n : ℕ}
  {α : Type}
  {C : FinitePlusTailClosedBallContractionCertificate n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {thermal : ℝ}
  {correlationLength : ℝ → ℝ}
-- given
  (hthermal : 1 < thermal)
  (hbridge : (C.certificate scale M thermal hthermal).RGToExponentBridge correlationLength) :
-- imply
  (C.certificate scale M thermal hthermal).Valid correlationLength where finiteCaseChecks := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.certificate_valid_of_bridge C scale M thermal hthermal correlationLength hbridge

/--
[certificate_rgToExponentBridge_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_hasCriticalNu_eq
  {n : ℕ}
  {α : Type}
  {C : FinitePlusTailClosedBallContractionCertificate n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {thermal : ℝ}
  {correlationLength : ℝ → ℝ}
-- given
  (hthermal : 1 < thermal)
  (hν : HasCriticalNu M correlationLength (C.certificate scale M thermal hthermal).predictedExponent) :
-- imply
  (C.certificate scale M thermal hthermal).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.certificate_rgToExponentBridge_of_hasCriticalNu C scale M thermal hthermal correlationLength hν

/--
[certificate_valid_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma certificate_valid_of_hasCriticalNu_eq
  {n : ℕ}
  {α : Type}
  {C : FinitePlusTailClosedBallContractionCertificate n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {thermal : ℝ}
  {correlationLength : ℝ → ℝ}
-- given
  (hthermal : 1 < thermal)
  (hν : HasCriticalNu M correlationLength (C.certificate scale M thermal hthermal).predictedExponent) :
-- imply
  (C.certificate scale M thermal hthermal).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.certificate_valid_of_hasCriticalNu C scale M thermal hthermal correlationLength hν

/--
[certificate_hasCriticalNu_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_bridge_eq
  {n : ℕ}
  {α : Type}
  {C : FinitePlusTailClosedBallContractionCertificate n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {thermal : ℝ}
  {correlationLength : ℝ → ℝ}
-- given
  (hthermal : 1 < thermal)
  (hbridge : (C.certificate scale M thermal hthermal).RGToExponentBridge correlationLength) :
-- imply
  HasCriticalNu M correlationLength (C.certificate scale M thermal hthermal).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.certificate_hasCriticalNu_of_bridge C scale M thermal hthermal correlationLength hbridge

/--
[with_larger_radius_certificate_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma with_larger_radius_certificate_eq_eq
  {n : ℕ}
  {α : Type}
  {C : FinitePlusTailClosedBallContractionCertificate n α}
  {radius' : ℝ}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {thermal : ℝ}
-- given
  (hradius : C.radius ≤ radius')
  (hthermal : 1 < thermal) :
-- imply
  (C.with_larger_radius hradius).certificate scale M thermal hthermal = C.certificate scale M thermal hthermal := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.with_larger_radius_certificate_eq C hradius scale M thermal hthermal

/--
[with_larger_radius_rgToExponentBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma with_larger_radius_rgToExponentBridge_eq
  {n : ℕ}
  {α : Type}
  {C : FinitePlusTailClosedBallContractionCertificate n α}
  {radius' : ℝ}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {thermal : ℝ}
  {correlationLength : ℝ → ℝ}
-- given
  (hradius : C.radius ≤ radius')
  (hthermal : 1 < thermal)
  (hbridge : (C.certificate scale M thermal hthermal).RGToExponentBridge correlationLength) :
-- imply
  ((C.with_larger_radius hradius).certificate scale M thermal hthermal).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.with_larger_radius_rgToExponentBridge C hradius scale M thermal hthermal hbridge

/--
[with_larger_radius_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma with_larger_radius_valid_eq
  {n : ℕ}
  {α : Type}
  {C : FinitePlusTailClosedBallContractionCertificate n α}
  {radius' : ℝ}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {thermal : ℝ}
  {correlationLength : ℝ → ℝ}
-- given
  (hradius : C.radius ≤ radius')
  (hthermal : 1 < thermal)
  (hvalid : (C.certificate scale M thermal hthermal).Valid correlationLength) :
-- imply
  ((C.with_larger_radius hradius).certificate scale M thermal hthermal).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.with_larger_radius_valid C hradius scale M thermal hthermal hvalid

/--
[with_larger_radius_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma with_larger_radius_hasCriticalNu_eq
  {n : ℕ}
  {α : Type}
  {C : FinitePlusTailClosedBallContractionCertificate n α}
  {radius' : ℝ}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {thermal : ℝ}
  {correlationLength : ℝ → ℝ}
-- given
  (hradius : C.radius ≤ radius')
  (hthermal : 1 < thermal)
  (hν : HasCriticalNu M correlationLength (C.certificate scale M thermal hthermal).predictedExponent) :
-- imply
  HasCriticalNu M correlationLength ((C.with_larger_radius hradius).certificate scale M thermal hthermal).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.with_larger_radius_hasCriticalNu C hradius scale M thermal hthermal hν

/--
[with_larger_residual_certificate_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma with_larger_residual_certificate_eq_eq
  {n : ℕ}
  {α : Type}
  {C : FinitePlusTailClosedBallContractionCertificate n α}
  {residual' : ℝ}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {thermal : ℝ}
-- given
  (hresidual : C.residual ≤ residual')
  (hbudget : residual' + C.contraction.c * C.radius ≤ C.radius)
  (hthermal : 1 < thermal) :
-- imply
  (C.with_larger_residual hresidual hbudget).certificate scale M thermal hthermal = C.certificate scale M thermal hthermal := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.with_larger_residual_certificate_eq C hresidual hbudget scale M thermal hthermal

/--
[with_larger_residual_rgToExponentBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma with_larger_residual_rgToExponentBridge_eq
  {n : ℕ}
  {α : Type}
  {C : FinitePlusTailClosedBallContractionCertificate n α}
  {residual' : ℝ}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {thermal : ℝ}
  {correlationLength : ℝ → ℝ}
-- given
  (hresidual : C.residual ≤ residual')
  (hbudget : residual' + C.contraction.c * C.radius ≤ C.radius)
  (hthermal : 1 < thermal)
  (hbridge : (C.certificate scale M thermal hthermal).RGToExponentBridge correlationLength) :
-- imply
  ((C.with_larger_residual hresidual hbudget).certificate scale M thermal hthermal).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.with_larger_residual_rgToExponentBridge C hresidual hbudget scale M thermal hthermal hbridge

/--
[with_larger_residual_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma with_larger_residual_valid_eq
  {n : ℕ}
  {α : Type}
  {C : FinitePlusTailClosedBallContractionCertificate n α}
  {residual' : ℝ}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {thermal : ℝ}
  {correlationLength : ℝ → ℝ}
-- given
  (hresidual : C.residual ≤ residual')
  (hbudget : residual' + C.contraction.c * C.radius ≤ C.radius)
  (hthermal : 1 < thermal)
  (hvalid : (C.certificate scale M thermal hthermal).Valid correlationLength) :
-- imply
  ((C.with_larger_residual hresidual hbudget).certificate scale M thermal hthermal).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.with_larger_residual_valid C hresidual hbudget scale M thermal hthermal hvalid

/--
[with_larger_residual_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma with_larger_residual_hasCriticalNu_eq
  {n : ℕ}
  {α : Type}
  {C : FinitePlusTailClosedBallContractionCertificate n α}
  {residual' : ℝ}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {thermal : ℝ}
  {correlationLength : ℝ → ℝ}
-- given
  (hresidual : C.residual ≤ residual')
  (hbudget : residual' + C.contraction.c * C.radius ≤ C.radius)
  (hthermal : 1 < thermal)
  (hν : HasCriticalNu M correlationLength (C.certificate scale M thermal hthermal).predictedExponent) :
-- imply
  HasCriticalNu M correlationLength ((C.with_larger_residual hresidual hbudget).certificate scale M thermal hthermal).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.with_larger_residual_hasCriticalNu C hresidual hbudget scale M thermal hthermal hν

/--
[certificate_retarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma certificate_retarget_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {N : CriticalModel κ} :
-- imply
  P.certificate scale N = (P.certificate scale M).retarget N := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_retarget P scale M N

/--
[certificate_thermalEigenvalue_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma certificate_thermalEigenvalue_eq_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι} :
-- imply
  (P.certificate scale M).thermalEigenvalue = P.thermal := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_thermalEigenvalue_eq P scale M

/--
[certificate_scale_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma certificate_scale_eq_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι} :
-- imply
  (P.certificate scale M).scale = scale := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_scale_eq P scale M

/--
[certificate_fixedPoint_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma certificate_fixedPoint_eq_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι} :
-- imply
  (P.certificate scale M).fixedPointData.fixedPoint = P.closedBall.fixedPoint := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_fixedPoint_eq P scale M

/--
[certificate_R_map_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma certificate_R_map_eq_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι} :
-- imply
  (P.certificate scale M).R.map = P.closedBall.contraction.map := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_R_map_eq P scale M

/--
[certificate_predictedExponent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma certificate_predictedExponent_eq_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι} :
-- imply
  (P.certificate scale M).predictedExponent = predictedNu scale P.thermal := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_predictedExponent_eq P scale M

/--
[mapsClosedBall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma mapsClosedBall_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α} :
-- imply
  FinitePlusTailState.MapsClosedBall P.closedBall.contraction.map P.closedBall.center P.closedBall.radius := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.mapsClosedBall P

/--
[fixedPoint_mem_closedBall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma fixedPoint_mem_closedBall_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α} :
-- imply
  FinitePlusTailState.ClosedBall P.closedBall.center P.closedBall.radius P.closedBall.fixedPoint := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.fixedPoint_mem_closedBall P

/--
[certificate_fixedPointEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma certificate_fixedPointEnclosure_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι} :
-- imply
  (P.certificate scale M).FixedPointEnclosure := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_fixedPointEnclosure P scale M

/--
[certificate_finiteCaseChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma certificate_finiteCaseChecks_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι} :
-- imply
  (P.certificate scale M).FiniteCaseChecks := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_finiteCaseChecks P scale M

/--
[certificate_tailBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma certificate_tailBounds_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι} :
-- imply
  (P.certificate scale M).TailBounds := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_tailBounds P scale M

/--
[certificate_linearizationEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma certificate_linearizationEnclosure_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι} :
-- imply
  (P.certificate scale M).LinearizationEnclosure := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_linearizationEnclosure P scale M

/--
[certificate_hyperbolicSplitting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma certificate_hyperbolicSplitting_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι} :
-- imply
  (P.certificate scale M).HyperbolicSplitting := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hyperbolicSplitting P scale M

/--
[certificate_orbitEntry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma certificate_orbitEntry_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι} :
-- imply
  (P.certificate scale M).OrbitEntry := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_orbitEntry P scale M

/--
[certificate_fixedPoint_mem_closedBall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma certificate_fixedPoint_mem_closedBall_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι} :
-- imply
  FinitePlusTailState.ClosedBall P.closedBall.center P.closedBall.radius (P.certificate scale M).fixedPointData.fixedPoint := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_fixedPoint_mem_closedBall P scale M

/--
[certificate_iterate_mem_closedBall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma certificate_iterate_mem_closedBall_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {x : (P.certificate scale M).H.carrier}
  {k : ℕ}
-- given
  (hx : FinitePlusTailState.ClosedBall P.closedBall.center P.closedBall.radius x) :
-- imply
  FinitePlusTailState.ClosedBall P.closedBall.center P.closedBall.radius ((((P.certificate scale M).R.map)^[k]) x) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_iterate_mem_closedBall P scale M hx k

/--
[certificate_valid_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma certificate_valid_of_bridge_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (hbridge : (P.certificate scale M).RGToExponentBridge correlationLength) :
-- imply
  (P.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_bridge P scale M correlationLength hbridge

/--
[certificate_rgToExponentBridge_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_hasCriticalNu_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (hν : HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent) :
-- imply
  (P.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_hasCriticalNu P scale M correlationLength hν

/--
[certificate_valid_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma certificate_valid_of_hasCriticalNu_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (hν : HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent) :
-- imply
  (P.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_hasCriticalNu P scale M correlationLength hν

/--
[certificate_hasCriticalNu_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_bridge_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (hbridge : (P.certificate scale M).RGToExponentBridge correlationLength) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_bridge P scale M correlationLength hbridge

/--
[certificate_rgToExponentBridge_of_bridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_bridge_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength) :
-- imply
  (P.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_bridge_congr_predictedExponent P scale M hpred hbridge

/--
[certificate_valid_of_bridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma certificate_valid_of_bridge_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength) :
-- imply
  (P.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_bridge_congr_predictedExponent P scale M hpred hbridge

/--
[certificate_hasCriticalNu_of_bridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_bridge_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_bridge_congr_predictedExponent P scale M hpred hbridge

/--
[certificate_retarget_rgToExponentBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma certificate_retarget_rgToExponentBridge_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength : ℝ → ℝ}
-- given
  (hbridge : (P.certificate scale M).RGToExponentBridge correlationLength)
  (hβc : M.betaC = N.betaC) :
-- imply
  (P.certificate scale N).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_retarget_rgToExponentBridge P scale M N hbridge hβc

/--
[certificate_retarget_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma certificate_retarget_valid_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength : ℝ → ℝ}
-- given
  (hvalid : (P.certificate scale M).Valid correlationLength)
  (hβc : M.betaC = N.betaC) :
-- imply
  (P.certificate scale N).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_retarget_valid P scale M N hvalid hβc

/--
[certificate_retarget_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma certificate_retarget_hasCriticalNu_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength : ℝ → ℝ}
-- given
  (hν : HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent)
  (hβc : M.betaC = N.betaC) :
-- imply
  HasCriticalNu N correlationLength (P.certificate scale N).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_retarget_hasCriticalNu P scale M N hν hβc

/--
[certificate_retarget_rgToExponentBridge_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma certificate_retarget_rgToExponentBridge_iff_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength : ℝ → ℝ}
-- given
  (hβc : M.betaC = N.betaC) :
-- imply
  (P.certificate scale M).RGToExponentBridge correlationLength ↔ (P.certificate scale N).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_retarget_rgToExponentBridge_iff P scale M N hβc

/--
[certificate_retarget_valid_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma certificate_retarget_valid_iff_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength : ℝ → ℝ}
-- given
  (hβc : M.betaC = N.betaC) :
-- imply
  (P.certificate scale M).Valid correlationLength ↔ (P.certificate scale N).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_retarget_valid_iff P scale M N hβc

/--
[certificate_retarget_hasCriticalNu_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma certificate_retarget_hasCriticalNu_iff_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength : ℝ → ℝ}
-- given
  (hβc : M.betaC = N.betaC) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent ↔ HasCriticalNu N correlationLength (P.certificate scale N).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_retarget_hasCriticalNu_iff P scale M N hβc

/--
[with_larger_radius_closedBall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma with_larger_radius_closedBall_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {radius' : ℝ}
-- given
  (hradius : P.closedBall.radius ≤ radius') :
-- imply
  (P.with_larger_radius hradius).closedBall = P.closedBall.with_larger_radius hradius := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.with_larger_radius_closedBall P hradius

/--
[with_larger_radius_closedBall_radius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma with_larger_radius_closedBall_radius_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {radius' : ℝ}
-- given
  (hradius : P.closedBall.radius ≤ radius') :
-- imply
  (P.with_larger_radius hradius).closedBall.radius = radius' := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.with_larger_radius_closedBall_radius P hradius

/--
[with_larger_radius_closedBall_fixedPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma with_larger_radius_closedBall_fixedPoint_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {radius' : ℝ}
-- given
  (hradius : P.closedBall.radius ≤ radius') :
-- imply
  (P.with_larger_radius hradius).closedBall.fixedPoint = P.closedBall.fixedPoint := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.with_larger_radius_closedBall_fixedPoint P hradius

/--
[with_larger_radius_thermal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma with_larger_radius_thermal_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {radius' : ℝ}
-- given
  (hradius : P.closedBall.radius ≤ radius') :
-- imply
  (P.with_larger_radius hradius).thermal = P.thermal := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.with_larger_radius_thermal P hradius

/--
[with_larger_radius_certificate_thermalEigenvalue_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma with_larger_radius_certificate_thermalEigenvalue_eq_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {radius' : ℝ}
  {scale : BlockScale}
  {M : CriticalModel ι}
-- given
  (hradius : P.closedBall.radius ≤ radius') :
-- imply
  ((P.with_larger_radius hradius).certificate scale M).thermalEigenvalue = P.thermal := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.with_larger_radius_certificate_thermalEigenvalue_eq P hradius scale M

/--
[with_larger_radius_certificate_scale_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma with_larger_radius_certificate_scale_eq_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {radius' : ℝ}
  {scale : BlockScale}
  {M : CriticalModel ι}
-- given
  (hradius : P.closedBall.radius ≤ radius') :
-- imply
  ((P.with_larger_radius hradius).certificate scale M).scale = scale := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.with_larger_radius_certificate_scale_eq P hradius scale M

/--
[with_larger_radius_certificate_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma with_larger_radius_certificate_eq_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {radius' : ℝ}
  {scale : BlockScale}
  {M : CriticalModel ι}
-- given
  (hradius : P.closedBall.radius ≤ radius') :
-- imply
  (P.with_larger_radius hradius).certificate scale M = P.certificate scale M := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.with_larger_radius_certificate_eq P hradius scale M

/--
[with_larger_radius_certificate_predictedExponent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma with_larger_radius_certificate_predictedExponent_eq_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {radius' : ℝ}
  {scale : BlockScale}
  {M : CriticalModel ι}
-- given
  (hradius : P.closedBall.radius ≤ radius') :
-- imply
  ((P.with_larger_radius hradius).certificate scale M).predictedExponent = (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.with_larger_radius_certificate_predictedExponent_eq P hradius scale M

/--
[with_larger_radius_rgToExponentBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma with_larger_radius_rgToExponentBridge_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {radius' : ℝ}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (hradius : P.closedBall.radius ≤ radius')
  (hbridge : (P.certificate scale M).RGToExponentBridge correlationLength) :
-- imply
  ((P.with_larger_radius hradius).certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.with_larger_radius_rgToExponentBridge P hradius scale M hbridge

/--
[with_larger_radius_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma with_larger_radius_valid_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {radius' : ℝ}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (hradius : P.closedBall.radius ≤ radius')
  (hvalid : (P.certificate scale M).Valid correlationLength) :
-- imply
  ((P.with_larger_radius hradius).certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.with_larger_radius_valid P hradius scale M hvalid

/--
[with_larger_radius_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma with_larger_radius_hasCriticalNu_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {radius' : ℝ}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (hradius : P.closedBall.radius ≤ radius')
  (hν : HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent) :
-- imply
  HasCriticalNu M correlationLength ((P.with_larger_radius hradius).certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.with_larger_radius_hasCriticalNu P hradius scale M hν

/--
[with_larger_residual_closedBall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma with_larger_residual_closedBall_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {residual' : ℝ}
-- given
  (hresidual : P.closedBall.residual ≤ residual')
  (hbudget : residual' + P.closedBall.contraction.c * P.closedBall.radius ≤ P.closedBall.radius) :
-- imply
  (P.with_larger_residual hresidual hbudget).closedBall = P.closedBall.with_larger_residual hresidual hbudget := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.with_larger_residual_closedBall P hresidual hbudget

/--
[with_larger_residual_closedBall_residual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma with_larger_residual_closedBall_residual_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {residual' : ℝ}
-- given
  (hresidual : P.closedBall.residual ≤ residual')
  (hbudget : residual' + P.closedBall.contraction.c * P.closedBall.radius ≤ P.closedBall.radius) :
-- imply
  (P.with_larger_residual hresidual hbudget).closedBall.residual = residual' := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.with_larger_residual_closedBall_residual P hresidual hbudget

/--
[with_larger_residual_closedBall_fixedPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma with_larger_residual_closedBall_fixedPoint_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {residual' : ℝ}
-- given
  (hresidual : P.closedBall.residual ≤ residual')
  (hbudget : residual' + P.closedBall.contraction.c * P.closedBall.radius ≤ P.closedBall.radius) :
-- imply
  (P.with_larger_residual hresidual hbudget).closedBall.fixedPoint = P.closedBall.fixedPoint := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.with_larger_residual_closedBall_fixedPoint P hresidual hbudget

/--
[with_larger_residual_thermal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma with_larger_residual_thermal_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {residual' : ℝ}
-- given
  (hresidual : P.closedBall.residual ≤ residual')
  (hbudget : residual' + P.closedBall.contraction.c * P.closedBall.radius ≤ P.closedBall.radius) :
-- imply
  (P.with_larger_residual hresidual hbudget).thermal = P.thermal := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.with_larger_residual_thermal P hresidual hbudget

/--
[with_larger_residual_certificate_thermalEigenvalue_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma with_larger_residual_certificate_thermalEigenvalue_eq_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {residual' : ℝ}
  {scale : BlockScale}
  {M : CriticalModel ι}
-- given
  (hresidual : P.closedBall.residual ≤ residual')
  (hbudget : residual' + P.closedBall.contraction.c * P.closedBall.radius ≤ P.closedBall.radius) :
-- imply
  ((P.with_larger_residual hresidual hbudget).certificate scale M).thermalEigenvalue = P.thermal := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.with_larger_residual_certificate_thermalEigenvalue_eq P hresidual hbudget scale M

/--
[with_larger_residual_certificate_scale_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma with_larger_residual_certificate_scale_eq_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {residual' : ℝ}
  {scale : BlockScale}
  {M : CriticalModel ι}
-- given
  (hresidual : P.closedBall.residual ≤ residual')
  (hbudget : residual' + P.closedBall.contraction.c * P.closedBall.radius ≤ P.closedBall.radius) :
-- imply
  ((P.with_larger_residual hresidual hbudget).certificate scale M).scale = scale := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.with_larger_residual_certificate_scale_eq P hresidual hbudget scale M

/--
[with_larger_residual_certificate_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma with_larger_residual_certificate_eq_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {residual' : ℝ}
  {scale : BlockScale}
  {M : CriticalModel ι}
-- given
  (hresidual : P.closedBall.residual ≤ residual')
  (hbudget : residual' + P.closedBall.contraction.c * P.closedBall.radius ≤ P.closedBall.radius) :
-- imply
  (P.with_larger_residual hresidual hbudget).certificate scale M = P.certificate scale M := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.with_larger_residual_certificate_eq P hresidual hbudget scale M

/--
[with_larger_residual_certificate_predictedExponent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma with_larger_residual_certificate_predictedExponent_eq_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {residual' : ℝ}
  {scale : BlockScale}
  {M : CriticalModel ι}
-- given
  (hresidual : P.closedBall.residual ≤ residual')
  (hbudget : residual' + P.closedBall.contraction.c * P.closedBall.radius ≤ P.closedBall.radius) :
-- imply
  ((P.with_larger_residual hresidual hbudget).certificate scale M).predictedExponent = (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.with_larger_residual_certificate_predictedExponent_eq P hresidual hbudget scale M

/--
[with_larger_residual_rgToExponentBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma with_larger_residual_rgToExponentBridge_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {residual' : ℝ}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (hresidual : P.closedBall.residual ≤ residual')
  (hbudget : residual' + P.closedBall.contraction.c * P.closedBall.radius ≤ P.closedBall.radius)
  (hbridge : (P.certificate scale M).RGToExponentBridge correlationLength) :
-- imply
  ((P.with_larger_residual hresidual hbudget).certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.with_larger_residual_rgToExponentBridge P hresidual hbudget scale M hbridge

/--
[with_larger_residual_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma with_larger_residual_valid_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {residual' : ℝ}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (hresidual : P.closedBall.residual ≤ residual')
  (hbudget : residual' + P.closedBall.contraction.c * P.closedBall.radius ≤ P.closedBall.radius)
  (hvalid : (P.certificate scale M).Valid correlationLength) :
-- imply
  ((P.with_larger_residual hresidual hbudget).certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.with_larger_residual_valid P hresidual hbudget scale M hvalid

/--
[with_larger_residual_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean)
-/
@[path]
private lemma with_larger_residual_hasCriticalNu_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {residual' : ℝ}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (hresidual : P.closedBall.residual ≤ residual')
  (hbudget : residual' + P.closedBall.contraction.c * P.closedBall.radius ≤ P.closedBall.radius)
  (hν : HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent) :
-- imply
  HasCriticalNu M correlationLength ((P.with_larger_residual hresidual hbudget).certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.with_larger_residual_hasCriticalNu P hresidual hbudget scale M hν


-- created on 2026-10-23

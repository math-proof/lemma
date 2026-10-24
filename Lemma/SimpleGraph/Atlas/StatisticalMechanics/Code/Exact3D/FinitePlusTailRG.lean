import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Exact3D.FinitePlusTailRG
open StatMech StatMech.Exact3D StatMech.Exact3D.FinitePlusTailHyperbolicSplitting


/--
[certificate_retarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailRG.lean)
-/
@[path]
private lemma certificate_retarget_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {N : CriticalModel κ} :
-- imply
  H.certificate scale N = (H.certificate scale M).retarget N := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_retarget H scale M N

/--
[certificate_fixedPointEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailRG.lean)
-/
@[path]
private lemma certificate_fixedPointEnclosure_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι} :
-- imply
  (H.certificate scale M).FixedPointEnclosure := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_fixedPointEnclosure H scale M

/--
[certificate_finiteCaseChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailRG.lean)
-/
@[path]
private lemma certificate_finiteCaseChecks_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι} :
-- imply
  (H.certificate scale M).FiniteCaseChecks := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_finiteCaseChecks H scale M

/--
[certificate_tailBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailRG.lean)
-/
@[path]
private lemma certificate_tailBounds_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι} :
-- imply
  (H.certificate scale M).TailBounds := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_tailBounds H scale M

/--
[certificate_linearizationEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailRG.lean)
-/
@[path]
private lemma certificate_linearizationEnclosure_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι} :
-- imply
  (H.certificate scale M).LinearizationEnclosure := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_linearizationEnclosure H scale M

/--
[certificate_hyperbolicSplitting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailRG.lean)
-/
@[path]
private lemma certificate_hyperbolicSplitting_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι} :
-- imply
  (H.certificate scale M).HyperbolicSplitting := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hyperbolicSplitting H scale M

/--
[certificate_orbitEntry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailRG.lean)
-/
@[path]
private lemma certificate_orbitEntry_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι} :
-- imply
  (H.certificate scale M).OrbitEntry := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_orbitEntry H scale M

/--
[rgMap_iterate_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailRG.lean)
-/
@[path]
private lemma rgMap_iterate_eq_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {k : ℕ}
  {x : State n α} :
-- imply
  ((H.rgMap scale).map^[k]) x = H.iterate k x := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.rgMap_iterate_eq H scale k x

/--
[rgMap_cone_iterate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailRG.lean)
-/
@[path]
private lemma rgMap_cone_iterate_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {η : ℝ}
  {x : State n α}
  {k : ℕ}
-- given
  (hη : 0 ≤ η)
  (hx : H.cone η x) :
-- imply
  H.cone η (((H.rgMap scale).map^[k]) x) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.rgMap_cone_iterate H scale hη hx k

/--
[certificate_cone_iterate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailRG.lean)
-/
@[path]
private lemma certificate_cone_iterate_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {η : ℝ}
  {x : (H.certificate scale M).H.carrier}
  {k : ℕ}
-- given
  (hη : 0 ≤ η)
  (hx : H.cone η x) :
-- imply
  H.cone η ((((H.certificate scale M).R.map)^[k]) x) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_cone_iterate H scale M hη hx k

/--
[certificate_valid_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailRG.lean)
-/
@[path]
private lemma certificate_valid_of_bridge_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (hbridge : (H.certificate scale M).RGToExponentBridge correlationLength) :
-- imply
  (H.certificate scale M).Valid correlationLength where finiteCaseChecks := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_bridge H scale M correlationLength hbridge

/--
[certificate_rgToExponentBridge_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailRG.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_hasCriticalNu_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (hν : HasCriticalNu M correlationLength (H.certificate scale M).predictedExponent) :
-- imply
  (H.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_hasCriticalNu H scale M correlationLength hν

/--
[certificate_valid_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailRG.lean)
-/
@[path]
private lemma certificate_valid_of_hasCriticalNu_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (hν : HasCriticalNu M correlationLength (H.certificate scale M).predictedExponent) :
-- imply
  (H.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_hasCriticalNu H scale M correlationLength hν

/--
[certificate_hasCriticalNu_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailRG.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_bridge_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (hbridge : (H.certificate scale M).RGToExponentBridge correlationLength) :
-- imply
  HasCriticalNu M correlationLength (H.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_bridge H scale M correlationLength hbridge

/--
[certificate_rgToExponentBridge_of_bridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailRG.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_bridge_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength) :
-- imply
  (H.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_bridge_congr_predictedExponent H scale M hpred hbridge

/--
[certificate_valid_of_bridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailRG.lean)
-/
@[path]
private lemma certificate_valid_of_bridge_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength) :
-- imply
  (H.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_bridge_congr_predictedExponent H scale M hpred hbridge

/--
[certificate_hasCriticalNu_of_bridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailRG.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_bridge_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength) :
-- imply
  HasCriticalNu M correlationLength (H.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_bridge_congr_predictedExponent H scale M hpred hbridge

/--
[certificate_retarget_rgToExponentBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailRG.lean)
-/
@[path]
private lemma certificate_retarget_rgToExponentBridge_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength : ℝ → ℝ}
-- given
  (hbridge : (H.certificate scale M).RGToExponentBridge correlationLength)
  (hβc : M.betaC = N.betaC) :
-- imply
  (H.certificate scale N).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_retarget_rgToExponentBridge H scale M N hbridge hβc

/--
[certificate_retarget_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailRG.lean)
-/
@[path]
private lemma certificate_retarget_valid_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength : ℝ → ℝ}
-- given
  (hvalid : (H.certificate scale M).Valid correlationLength)
  (hβc : M.betaC = N.betaC) :
-- imply
  (H.certificate scale N).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_retarget_valid H scale M N hvalid hβc

/--
[certificate_retarget_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailRG.lean)
-/
@[path]
private lemma certificate_retarget_hasCriticalNu_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength : ℝ → ℝ}
-- given
  (hν : HasCriticalNu M correlationLength (H.certificate scale M).predictedExponent)
  (hβc : M.betaC = N.betaC) :
-- imply
  HasCriticalNu N correlationLength (H.certificate scale N).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_retarget_hasCriticalNu H scale M N hν hβc

/--
[certificate_retarget_rgToExponentBridge_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailRG.lean)
-/
@[path]
private lemma certificate_retarget_rgToExponentBridge_iff_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength : ℝ → ℝ}
-- given
  (hβc : M.betaC = N.betaC) :
-- imply
  (H.certificate scale M).RGToExponentBridge correlationLength ↔ (H.certificate scale N).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_retarget_rgToExponentBridge_iff H scale M N hβc

/--
[certificate_retarget_valid_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailRG.lean)
-/
@[path]
private lemma certificate_retarget_valid_iff_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength : ℝ → ℝ}
-- given
  (hβc : M.betaC = N.betaC) :
-- imply
  (H.certificate scale M).Valid correlationLength ↔ (H.certificate scale N).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_retarget_valid_iff H scale M N hβc

/--
[certificate_retarget_hasCriticalNu_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailRG.lean)
-/
@[path]
private lemma certificate_retarget_hasCriticalNu_iff_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength : ℝ → ℝ}
-- given
  (hβc : M.betaC = N.betaC) :
-- imply
  HasCriticalNu M correlationLength (H.certificate scale M).predictedExponent ↔ HasCriticalNu N correlationLength (H.certificate scale N).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_retarget_hasCriticalNu_iff H scale M N hβc


-- created on 2026-10-23

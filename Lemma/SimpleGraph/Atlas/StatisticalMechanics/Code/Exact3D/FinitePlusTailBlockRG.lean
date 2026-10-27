import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailBlockRG.Part5
open StatMech StatMech.Exact3D StatMech.Exact3D.FinitePlusTailBlockRGPackage


/--
[stableCertificate_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma stableCertificate_map_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α} :
-- imply
  P.stableCertificate.map = P.blockBounds.map := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.stableCertificate_map P

/--
[stableCertificate_c](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma stableCertificate_c_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α} :
-- imply
  P.stableCertificate.c = P.c := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.stableCertificate_c P

/--
[stableCertificate_finiteToFinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma stableCertificate_finiteToFinite_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α} :
-- imply
  P.stableCertificate.finiteToFinite = P.blockBounds.finiteToFinite := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.stableCertificate_finiteToFinite P

/--
[stableCertificate_tailToFinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma stableCertificate_tailToFinite_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α} :
-- imply
  P.stableCertificate.tailToFinite = P.blockBounds.tailToFinite := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.stableCertificate_tailToFinite P

/--
[stableCertificate_finiteToTail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma stableCertificate_finiteToTail_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α} :
-- imply
  P.stableCertificate.finiteToTail = P.blockBounds.finiteToTail := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.stableCertificate_finiteToTail P

/--
[stableCertificate_tailToTail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma stableCertificate_tailToTail_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α} :
-- imply
  P.stableCertificate.tailToTail = P.blockBounds.tailToTail := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.stableCertificate_tailToTail P

/--
[with_larger_c_blockBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma with_larger_c_blockBounds_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {c' : ℝ}
-- given
  (hc : P.c ≤ c')
  (hc_lt_one : c' < 1)
  (hdominated : c' ≤ |P.thermal|) :
-- imply
  (P.with_larger_c hc hc_lt_one hdominated).blockBounds = P.blockBounds := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.with_larger_c_blockBounds P hc hc_lt_one hdominated

/--
[with_larger_c_c](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma with_larger_c_c_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {c' : ℝ}
-- given
  (hc : P.c ≤ c')
  (hc_lt_one : c' < 1)
  (hdominated : c' ≤ |P.thermal|) :
-- imply
  (P.with_larger_c hc hc_lt_one hdominated).c = c' := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.with_larger_c_c P hc hc_lt_one hdominated

/--
[with_larger_c_thermal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma with_larger_c_thermal_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {c' : ℝ}
-- given
  (hc : P.c ≤ c')
  (hc_lt_one : c' < 1)
  (hdominated : c' ≤ |P.thermal|) :
-- imply
  (P.with_larger_c hc hc_lt_one hdominated).thermal = P.thermal := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.with_larger_c_thermal P hc hc_lt_one hdominated

/--
[with_larger_constants_c](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma with_larger_constants_c_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {finiteToFinite' tailToFinite' finiteToTail' tailToTail' c' : ℝ}
-- given
  (hff : P.blockBounds.finiteToFinite ≤ finiteToFinite')
  (htf : P.blockBounds.tailToFinite ≤ tailToFinite')
  (hft : P.blockBounds.finiteToTail ≤ finiteToTail')
  (htt : P.blockBounds.tailToTail ≤ tailToTail')
  (hc_nonneg : 0 ≤ c')
  (hc_lt_one : c' < 1)
  (hfinite_column_sum_le : finiteToFinite' + finiteToTail' ≤ c')
  (htail_column_sum_le : tailToFinite' + tailToTail' ≤ c')
  (hdominated : c' ≤ |P.thermal|) :
-- imply
  (P.with_larger_constants hff htf hft htt hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le hdominated).c = c' := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.with_larger_constants_c P hff htf hft htt hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le hdominated

/--
[with_larger_constants_blockBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma with_larger_constants_blockBounds_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {finiteToFinite' tailToFinite' finiteToTail' tailToTail' c' : ℝ}
-- given
  (hff : P.blockBounds.finiteToFinite ≤ finiteToFinite')
  (htf : P.blockBounds.tailToFinite ≤ tailToFinite')
  (hft : P.blockBounds.finiteToTail ≤ finiteToTail')
  (htt : P.blockBounds.tailToTail ≤ tailToTail')
  (hc_nonneg : 0 ≤ c')
  (hc_lt_one : c' < 1)
  (hfinite_column_sum_le : finiteToFinite' + finiteToTail' ≤ c')
  (htail_column_sum_le : tailToFinite' + tailToTail' ≤ c')
  (hdominated : c' ≤ |P.thermal|) :
-- imply
  (P.with_larger_constants hff htf hft htt hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le hdominated).blockBounds = P.blockBounds.with_larger_constants hff htf hft htt := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.with_larger_constants_blockBounds P hff htf hft htt hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le hdominated

/--
[with_larger_constants_thermal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma with_larger_constants_thermal_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {finiteToFinite' tailToFinite' finiteToTail' tailToTail' c' : ℝ}
-- given
  (hff : P.blockBounds.finiteToFinite ≤ finiteToFinite')
  (htf : P.blockBounds.tailToFinite ≤ tailToFinite')
  (hft : P.blockBounds.finiteToTail ≤ finiteToTail')
  (htt : P.blockBounds.tailToTail ≤ tailToTail')
  (hc_nonneg : 0 ≤ c')
  (hc_lt_one : c' < 1)
  (hfinite_column_sum_le : finiteToFinite' + finiteToTail' ≤ c')
  (htail_column_sum_le : tailToFinite' + tailToTail' ≤ c')
  (hdominated : c' ≤ |P.thermal|) :
-- imply
  (P.with_larger_constants hff htf hft htt hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le hdominated).thermal = P.thermal := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.with_larger_constants_thermal P hff htf hft htt hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le hdominated

/--
[with_larger_constants_stableCertificate_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma with_larger_constants_stableCertificate_map_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {finiteToFinite' tailToFinite' finiteToTail' tailToTail' c' : ℝ}
-- given
  (hff : P.blockBounds.finiteToFinite ≤ finiteToFinite')
  (htf : P.blockBounds.tailToFinite ≤ tailToFinite')
  (hft : P.blockBounds.finiteToTail ≤ finiteToTail')
  (htt : P.blockBounds.tailToTail ≤ tailToTail')
  (hc_nonneg : 0 ≤ c')
  (hc_lt_one : c' < 1)
  (hfinite_column_sum_le : finiteToFinite' + finiteToTail' ≤ c')
  (htail_column_sum_le : tailToFinite' + tailToTail' ≤ c')
  (hdominated : c' ≤ |P.thermal|) :
-- imply
  ((P.with_larger_constants hff htf hft htt hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le hdominated).stableCertificate).map = P.stableCertificate.map := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.with_larger_constants_stableCertificate_map P hff htf hft htt hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le hdominated

/--
[hyperbolicSplitting_thermal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma hyperbolicSplitting_thermal_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α} :
-- imply
  P.hyperbolicSplitting.thermal = P.thermal := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.hyperbolicSplitting_thermal P

/--
[hyperbolicSplitting_stable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma hyperbolicSplitting_stable_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α} :
-- imply
  P.hyperbolicSplitting.stable = P.stableCertificate := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.hyperbolicSplitting_stable P

/--
[with_larger_c_hyperbolicSplitting_stable_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma with_larger_c_hyperbolicSplitting_stable_map_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {c' : ℝ}
-- given
  (hc : P.c ≤ c')
  (hc_lt_one : c' < 1)
  (hdominated : c' ≤ |P.thermal|) :
-- imply
  (P.with_larger_c hc hc_lt_one hdominated).hyperbolicSplitting.stable.map = P.hyperbolicSplitting.stable.map := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.with_larger_c_hyperbolicSplitting_stable_map P hc hc_lt_one hdominated

/--
[with_larger_constants_hyperbolicSplitting_stable_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma with_larger_constants_hyperbolicSplitting_stable_map_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {finiteToFinite' tailToFinite' finiteToTail' tailToTail' c' : ℝ}
-- given
  (hff : P.blockBounds.finiteToFinite ≤ finiteToFinite')
  (htf : P.blockBounds.tailToFinite ≤ tailToFinite')
  (hft : P.blockBounds.finiteToTail ≤ finiteToTail')
  (htt : P.blockBounds.tailToTail ≤ tailToTail')
  (hc_nonneg : 0 ≤ c')
  (hc_lt_one : c' < 1)
  (hfinite_column_sum_le : finiteToFinite' + finiteToTail' ≤ c')
  (htail_column_sum_le : tailToFinite' + tailToTail' ≤ c')
  (hdominated : c' ≤ |P.thermal|) :
-- imply
  (let Q := P.with_larger_constants hff htf hft htt hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le hdominated; Q.hyperbolicSplitting.stable.map = P.hyperbolicSplitting.stable.map) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.with_larger_constants_hyperbolicSplitting_stable_map P hff htf hft htt hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le hdominated

/--
[cone_iterate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma cone_iterate_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {η : ℝ}
  {x : FinitePlusTailHyperbolicSplitting.State n α}
  {k : ℕ}
-- given
  (hη : 0 ≤ η)
  (hx : P.hyperbolicSplitting.cone η x) :
-- imply
  P.hyperbolicSplitting.cone η (P.hyperbolicSplitting.iterate k x) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.cone_iterate P hη hx k

/--
[certificate_retarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma certificate_retarget_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {N : CriticalModel κ} :
-- imply
  P.certificate scale N = (P.certificate scale M).retarget N := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_retarget P scale M N

/--
[certificate_thermalEigenvalue_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma certificate_thermalEigenvalue_eq_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι} :
-- imply
  (P.certificate scale M).thermalEigenvalue = P.thermal := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_thermalEigenvalue_eq P scale M

/--
[certificate_scale_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma certificate_scale_eq_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι} :
-- imply
  (P.certificate scale M).scale = scale := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_scale_eq P scale M

/--
[certificate_predictedExponent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma certificate_predictedExponent_eq_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι} :
-- imply
  (P.certificate scale M).predictedExponent = predictedNu scale P.thermal := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_predictedExponent_eq P scale M

/--
[with_larger_c_certificate_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma with_larger_c_certificate_eq_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {c' : ℝ}
  {scale : BlockScale}
  {M : CriticalModel ι}
-- given
  (hc : P.c ≤ c')
  (hc_lt_one : c' < 1)
  (hdominated : c' ≤ |P.thermal|) :
-- imply
  (P.with_larger_c hc hc_lt_one hdominated).certificate scale M = P.certificate scale M := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.with_larger_c_certificate_eq P hc hc_lt_one hdominated scale M

/--
[with_larger_c_certificate_predictedExponent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma with_larger_c_certificate_predictedExponent_eq_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {c' : ℝ}
  {scale : BlockScale}
  {M : CriticalModel ι}
-- given
  (hc : P.c ≤ c')
  (hc_lt_one : c' < 1)
  (hdominated : c' ≤ |P.thermal|) :
-- imply
  ((P.with_larger_c hc hc_lt_one hdominated).certificate scale M).predictedExponent = (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.with_larger_c_certificate_predictedExponent_eq P hc hc_lt_one hdominated scale M

/--
[with_larger_c_rgToExponentBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma with_larger_c_rgToExponentBridge_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {c' : ℝ}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (hc : P.c ≤ c')
  (hc_lt_one : c' < 1)
  (hdominated : c' ≤ |P.thermal|)
  (hbridge : (P.certificate scale M).RGToExponentBridge correlationLength) :
-- imply
  ((P.with_larger_c hc hc_lt_one hdominated).certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.with_larger_c_rgToExponentBridge P hc hc_lt_one hdominated scale M hbridge

/--
[with_larger_c_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma with_larger_c_valid_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {c' : ℝ}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (hc : P.c ≤ c')
  (hc_lt_one : c' < 1)
  (hdominated : c' ≤ |P.thermal|)
  (hvalid : (P.certificate scale M).Valid correlationLength) :
-- imply
  ((P.with_larger_c hc hc_lt_one hdominated).certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.with_larger_c_valid P hc hc_lt_one hdominated scale M hvalid

/--
[with_larger_c_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma with_larger_c_hasCriticalNu_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {c' : ℝ}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (hc : P.c ≤ c')
  (hc_lt_one : c' < 1)
  (hdominated : c' ≤ |P.thermal|)
  (hν : HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent) :
-- imply
  HasCriticalNu M correlationLength ((P.with_larger_c hc hc_lt_one hdominated).certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.with_larger_c_hasCriticalNu P hc hc_lt_one hdominated scale M hν

/--
[with_larger_constants_certificate_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma with_larger_constants_certificate_eq_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {finiteToFinite' tailToFinite' finiteToTail' tailToTail' c' : ℝ}
  {scale : BlockScale}
  {M : CriticalModel ι}
-- given
  (hff : P.blockBounds.finiteToFinite ≤ finiteToFinite')
  (htf : P.blockBounds.tailToFinite ≤ tailToFinite')
  (hft : P.blockBounds.finiteToTail ≤ finiteToTail')
  (htt : P.blockBounds.tailToTail ≤ tailToTail')
  (hc_nonneg : 0 ≤ c')
  (hc_lt_one : c' < 1)
  (hfinite_column_sum_le : finiteToFinite' + finiteToTail' ≤ c')
  (htail_column_sum_le : tailToFinite' + tailToTail' ≤ c')
  (hdominated : c' ≤ |P.thermal|) :
-- imply
  (P.with_larger_constants hff htf hft htt hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le hdominated).certificate scale M = P.certificate scale M := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.with_larger_constants_certificate_eq P hff htf hft htt hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le hdominated scale M

/--
[with_larger_constants_certificate_predictedExponent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma with_larger_constants_certificate_predictedExponent_eq_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {finiteToFinite' tailToFinite' finiteToTail' tailToTail' c' : ℝ}
  {scale : BlockScale}
  {M : CriticalModel ι}
-- given
  (hff : P.blockBounds.finiteToFinite ≤ finiteToFinite')
  (htf : P.blockBounds.tailToFinite ≤ tailToFinite')
  (hft : P.blockBounds.finiteToTail ≤ finiteToTail')
  (htt : P.blockBounds.tailToTail ≤ tailToTail')
  (hc_nonneg : 0 ≤ c')
  (hc_lt_one : c' < 1)
  (hfinite_column_sum_le : finiteToFinite' + finiteToTail' ≤ c')
  (htail_column_sum_le : tailToFinite' + tailToTail' ≤ c')
  (hdominated : c' ≤ |P.thermal|) :
-- imply
  ((P.with_larger_constants hff htf hft htt hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le hdominated).certificate scale M).predictedExponent = (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.with_larger_constants_certificate_predictedExponent_eq P hff htf hft htt hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le hdominated scale M

/--
[with_larger_constants_rgToExponentBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma with_larger_constants_rgToExponentBridge_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {finiteToFinite' tailToFinite' finiteToTail' tailToTail' c' : ℝ}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (hff : P.blockBounds.finiteToFinite ≤ finiteToFinite')
  (htf : P.blockBounds.tailToFinite ≤ tailToFinite')
  (hft : P.blockBounds.finiteToTail ≤ finiteToTail')
  (htt : P.blockBounds.tailToTail ≤ tailToTail')
  (hc_nonneg : 0 ≤ c')
  (hc_lt_one : c' < 1)
  (hfinite_column_sum_le : finiteToFinite' + finiteToTail' ≤ c')
  (htail_column_sum_le : tailToFinite' + tailToTail' ≤ c')
  (hdominated : c' ≤ |P.thermal|)
  (hbridge : (P.certificate scale M).RGToExponentBridge correlationLength) :
-- imply
  ((P.with_larger_constants hff htf hft htt hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le hdominated).certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.with_larger_constants_rgToExponentBridge P hff htf hft htt hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le hdominated scale M hbridge

/--
[with_larger_constants_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma with_larger_constants_valid_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {finiteToFinite' tailToFinite' finiteToTail' tailToTail' c' : ℝ}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (hff : P.blockBounds.finiteToFinite ≤ finiteToFinite')
  (htf : P.blockBounds.tailToFinite ≤ tailToFinite')
  (hft : P.blockBounds.finiteToTail ≤ finiteToTail')
  (htt : P.blockBounds.tailToTail ≤ tailToTail')
  (hc_nonneg : 0 ≤ c')
  (hc_lt_one : c' < 1)
  (hfinite_column_sum_le : finiteToFinite' + finiteToTail' ≤ c')
  (htail_column_sum_le : tailToFinite' + tailToTail' ≤ c')
  (hdominated : c' ≤ |P.thermal|)
  (hvalid : (P.certificate scale M).Valid correlationLength) :
-- imply
  ((P.with_larger_constants hff htf hft htt hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le hdominated).certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.with_larger_constants_valid P hff htf hft htt hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le hdominated scale M hvalid

/--
[with_larger_constants_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma with_larger_constants_hasCriticalNu_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {finiteToFinite' tailToFinite' finiteToTail' tailToTail' c' : ℝ}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (hff : P.blockBounds.finiteToFinite ≤ finiteToFinite')
  (htf : P.blockBounds.tailToFinite ≤ tailToFinite')
  (hft : P.blockBounds.finiteToTail ≤ finiteToTail')
  (htt : P.blockBounds.tailToTail ≤ tailToTail')
  (hc_nonneg : 0 ≤ c')
  (hc_lt_one : c' < 1)
  (hfinite_column_sum_le : finiteToFinite' + finiteToTail' ≤ c')
  (htail_column_sum_le : tailToFinite' + tailToTail' ≤ c')
  (hdominated : c' ≤ |P.thermal|)
  (hν : HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent) :
-- imply
  HasCriticalNu M correlationLength ((P.with_larger_constants hff htf hft htt hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le hdominated).certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.with_larger_constants_hasCriticalNu P hff htf hft htt hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le hdominated scale M hν

/--
[certificate_fixedPointEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma certificate_fixedPointEnclosure_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι} :
-- imply
  (P.certificate scale M).FixedPointEnclosure := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_fixedPointEnclosure P scale M

/--
[certificate_finiteCaseChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma certificate_finiteCaseChecks_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι} :
-- imply
  (P.certificate scale M).FiniteCaseChecks := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_finiteCaseChecks P scale M

/--
[certificate_tailBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma certificate_tailBounds_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι} :
-- imply
  (P.certificate scale M).TailBounds := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_tailBounds P scale M

/--
[certificate_linearizationEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma certificate_linearizationEnclosure_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι} :
-- imply
  (P.certificate scale M).LinearizationEnclosure := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_linearizationEnclosure P scale M

/--
[certificate_hyperbolicSplitting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma certificate_hyperbolicSplitting_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι} :
-- imply
  (P.certificate scale M).HyperbolicSplitting := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hyperbolicSplitting P scale M

/--
[certificate_orbitEntry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma certificate_orbitEntry_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι} :
-- imply
  (P.certificate scale M).OrbitEntry := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_orbitEntry P scale M

/--
[certificate_cone_iterate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma certificate_cone_iterate_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {η : ℝ}
  {x : (P.certificate scale M).H.carrier}
  {k : ℕ}
-- given
  (hη : 0 ≤ η)
  (hx : P.hyperbolicSplitting.cone η x) :
-- imply
  P.hyperbolicSplitting.cone η ((((P.certificate scale M).R.map)^[k]) x) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_cone_iterate P scale M hη hx k

/--
[certificate_valid_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma certificate_valid_of_bridge_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (hbridge : (P.certificate scale M).RGToExponentBridge correlationLength) :
-- imply
  (P.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_bridge P scale M correlationLength hbridge

/--
[certificate_rgToExponentBridge_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_hasCriticalNu_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (hν : HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent) :
-- imply
  (P.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_hasCriticalNu P scale M correlationLength hν

/--
[certificate_valid_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma certificate_valid_of_hasCriticalNu_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (hν : HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent) :
-- imply
  (P.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_hasCriticalNu P scale M correlationLength hν

/--
[certificate_hasCriticalNu_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_bridge_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (hbridge : (P.certificate scale M).RGToExponentBridge correlationLength) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_bridge P scale M correlationLength hbridge

/--
[certificate_rgToExponentBridge_of_bridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_bridge_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
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
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_bridge_congr_predictedExponent P scale M hpred hbridge

/--
[certificate_valid_of_bridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma certificate_valid_of_bridge_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
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
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_bridge_congr_predictedExponent P scale M hpred hbridge

/--
[certificate_hasCriticalNu_of_bridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_bridge_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
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
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_bridge_congr_predictedExponent P scale M hpred hbridge

/--
[certificate_retarget_rgToExponentBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma certificate_retarget_rgToExponentBridge_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
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
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_retarget_rgToExponentBridge P scale M N hbridge hβc

/--
[certificate_retarget_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma certificate_retarget_valid_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
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
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_retarget_valid P scale M N hvalid hβc

/--
[certificate_retarget_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma certificate_retarget_hasCriticalNu_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
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
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_retarget_hasCriticalNu P scale M N hν hβc

/--
[certificate_retarget_rgToExponentBridge_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma certificate_retarget_rgToExponentBridge_iff_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength : ℝ → ℝ}
-- given
  (hβc : M.betaC = N.betaC) :
-- imply
  (P.certificate scale M).RGToExponentBridge correlationLength ↔ (P.certificate scale N).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_retarget_rgToExponentBridge_iff P scale M N hβc

/--
[certificate_retarget_valid_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma certificate_retarget_valid_iff_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength : ℝ → ℝ}
-- given
  (hβc : M.betaC = N.betaC) :
-- imply
  (P.certificate scale M).Valid correlationLength ↔ (P.certificate scale N).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_retarget_valid_iff P scale M N hβc

/--
[certificate_retarget_hasCriticalNu_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean)
-/
@[path]
private lemma certificate_retarget_hasCriticalNu_iff_eq
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength : ℝ → ℝ}
-- given
  (hβc : M.betaC = N.betaC) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent ↔ HasCriticalNu N correlationLength (P.certificate scale N).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_retarget_hasCriticalNu_iff P scale M N hβc


-- created on 2026-10-23

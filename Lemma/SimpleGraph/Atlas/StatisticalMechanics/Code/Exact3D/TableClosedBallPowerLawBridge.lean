import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.TableClosedBallPowerLawBridge
open StatMech StatMech.Exact3D StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage


/--
[certificate_rgToExponentBridge_of_eventually_exact_power_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_eventually_exact_power_prefactor_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hA : 0 < A)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A * Real.exp (-(P.certificate scale).predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_eventually_exact_power_prefactor P scale correlationLength hA hξ

/--
[certificate_valid_of_eventually_exact_power_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_eventually_exact_power_prefactor_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hA : 0 < A)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A * Real.exp (-(P.certificate scale).predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_eventually_exact_power_prefactor P scale correlationLength hA hξ

/--
[certificate_hasCriticalNu_of_eventually_exact_power_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_eventually_exact_power_prefactor_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hA : 0 < A)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A * Real.exp (-(P.certificate scale).predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_eventually_exact_power_prefactor P scale correlationLength hA hξ

/--
[certificate_rgToExponentBridge_of_eventually_exact_power_prefactor_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_eventually_exact_power_prefactor_congr_pred_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (hA : 0 < A)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_eventually_exact_power_prefactor_congr_pred P scale D correlationLength hpred hA hξ

/--
[certificate_rgToExponentBridge_of_eventually_exact_power_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_eventually_exact_power_prefactor_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (hA : 0 < A)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_eventually_exact_power_prefactor_congr_predictedExponent P scale D correlationLength hpred hA hξ

/--
[certificate_valid_of_eventually_exact_power_prefactor_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_eventually_exact_power_prefactor_congr_pred_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (hA : 0 < A)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_eventually_exact_power_prefactor_congr_pred P scale D correlationLength hpred hA hξ

/--
[certificate_hasCriticalNu_of_eventually_exact_power_prefactor_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_eventually_exact_power_prefactor_congr_pred_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (hA : 0 < A)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_eventually_exact_power_prefactor_congr_pred P scale D correlationLength hpred hA hξ

/--
[certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
  {δ : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hA : 0 < A)
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A * Real.exp (-(P.certificate scale).predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo P scale correlationLength δ hA hδ hξ

/--
[certificate_valid_of_exact_power_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_exact_power_prefactor_on_Ioo_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
  {δ : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hA : 0 < A)
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A * Real.exp (-(P.certificate scale).predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_exact_power_prefactor_on_Ioo P scale correlationLength δ hA hδ hξ

/--
[certificate_hasCriticalNu_of_exact_power_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_exact_power_prefactor_on_Ioo_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
  {δ : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hA : 0 < A)
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A * Real.exp (-(P.certificate scale).predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_exact_power_prefactor_on_Ioo P scale correlationLength δ hA hδ hξ

/--
[certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_pred_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
  {δ : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (hA : 0 < A)
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_pred P scale D correlationLength δ hpred hA hδ hξ

/--
[certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
  {δ : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (hA : 0 < A)
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent P scale D correlationLength δ hpred hA hδ hξ

/--
[certificate_valid_of_exact_power_prefactor_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_exact_power_prefactor_on_Ioo_congr_pred_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
  {δ : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (hA : 0 < A)
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_exact_power_prefactor_on_Ioo_congr_pred P scale D correlationLength δ hpred hA hδ hξ

/--
[certificate_hasCriticalNu_of_exact_power_prefactor_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_exact_power_prefactor_on_Ioo_congr_pred_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
  {δ : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (hA : 0 < A)
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_exact_power_prefactor_on_Ioo_congr_pred P scale D correlationLength δ hpred hA hδ hξ

/--
[certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {correlationLength A : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-(P.certificate scale).predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor P scale correlationLength A hA hlogA hξ

/--
[certificate_valid_of_eventually_exact_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_eventually_exact_power_variable_prefactor_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {correlationLength A : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-(P.certificate scale).predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_eventually_exact_power_variable_prefactor P scale correlationLength A hA hlogA hξ

/--
[certificate_hasCriticalNu_of_eventually_exact_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_eventually_exact_power_variable_prefactor_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {correlationLength A : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-(P.certificate scale).predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_eventually_exact_power_variable_prefactor P scale correlationLength A hA hlogA hξ

/--
[certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_pred_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_pred P scale D correlationLength A hpred hA hlogA hξ

/--
[certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_predictedExponent P scale D correlationLength A hpred hA hlogA hξ

/--
[certificate_valid_of_eventually_exact_power_variable_prefactor_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_eventually_exact_power_variable_prefactor_congr_pred_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_eventually_exact_power_variable_prefactor_congr_pred P scale D correlationLength A hpred hA hlogA hξ

/--
[certificate_hasCriticalNu_of_eventually_exact_power_variable_prefactor_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_eventually_exact_power_variable_prefactor_congr_pred_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_eventually_exact_power_variable_prefactor_congr_pred P scale D correlationLength A hpred hA hlogA hξ

/--
[certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-(P.certificate scale).predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo P scale correlationLength A δ hδ hA hlogA hξ

/--
[certificate_valid_of_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_exact_power_variable_prefactor_on_Ioo_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-(P.certificate scale).predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_exact_power_variable_prefactor_on_Ioo P scale correlationLength A δ hδ hA hlogA hξ

/--
[certificate_hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-(P.certificate scale).predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo P scale correlationLength A δ hδ hA hlogA hξ

/--
[certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_pred_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_pred P scale D correlationLength A δ hpred hδ hA hlogA hξ

/--
[certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent P scale D correlationLength A δ hpred hδ hA hlogA hξ

/--
[certificate_valid_of_exact_power_variable_prefactor_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_exact_power_variable_prefactor_on_Ioo_congr_pred_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_exact_power_variable_prefactor_on_Ioo_congr_pred P scale D correlationLength A δ hpred hδ hA hlogA hξ

/--
[certificate_hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo_congr_pred_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo_congr_pred P scale D correlationLength A δ hpred hδ hA hlogA hξ

/--
[certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp ((P.certificate scale).predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  (P.certificate scale).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor P scale correlationLength mass B hB hlogB hmass hξ

/--
[certificate_valid_of_eventually_exact_mass_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_eventually_exact_mass_power_variable_prefactor_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp ((P.certificate scale).predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  (P.certificate scale).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_eventually_exact_mass_power_variable_prefactor P scale correlationLength mass B hB hlogB hmass hξ

/--
[certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp ((P.certificate scale).predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor P scale correlationLength mass B hB hlogB hmass hξ

/--
[certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_pred_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  (P.certificate scale).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_pred P scale D correlationLength mass B hpred hB hlogB hmass hξ

/--
[certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  (P.certificate scale).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent P scale D correlationLength mass B hpred hB hlogB hmass hξ

/--
[certificate_valid_of_eventually_exact_mass_power_variable_prefactor_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_eventually_exact_mass_power_variable_prefactor_congr_pred_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  (P.certificate scale).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_eventually_exact_mass_power_variable_prefactor_congr_pred P scale D correlationLength mass B hpred hB hlogB hmass hξ

/--
[certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_pred_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_pred P scale D correlationLength mass B hpred hB hlogB hmass hξ

/--
[certificate_valid_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  (P.certificate scale).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent P scale D correlationLength mass B hpred hB hlogB hmass hξ

/--
[certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent P scale D correlationLength mass B hpred hB hlogB hmass hξ

/--
[certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp ((P.certificate scale).predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  (P.certificate scale).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo P scale correlationLength mass B δ hδ hB hlogB hmass hξ

/--
[certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp ((P.certificate scale).predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  (P.certificate scale).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo P scale correlationLength mass B δ hδ hB hlogB hmass hξ

/--
[certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp ((P.certificate scale).predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo P scale correlationLength mass B δ hδ hB hlogB hmass hξ

/--
[certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  (P.certificate scale).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred P scale D correlationLength mass B δ hpred hδ hB hlogB hmass hξ

/--
[certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  (P.certificate scale).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent P scale D correlationLength mass B δ hpred hδ hB hlogB hmass hξ

/--
[certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  (P.certificate scale).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred P scale D correlationLength mass B δ hpred hδ hB hlogB hmass hξ

/--
[certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred P scale D correlationLength mass B δ hpred hδ hB hlogB hmass hξ

/--
[certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  (P.certificate scale).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent P scale D correlationLength mass B δ hpred hδ hB hlogB hmass hξ

/--
[certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent P scale D correlationLength mass B δ hpred hδ hB hlogB hmass hξ


-- created on 2026-10-23

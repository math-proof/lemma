import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.SLE.FKIsingDrivingReduction
open Filter MeasureTheory StatMech StatMech.SLE


/--
[fkIsingObservableJet_secondCoeff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/FKIsingDrivingReduction.lean)
-/
@[path]
private lemma fkIsingObservableJet_secondCoeff_eq
  {t W : Real} :
-- imply
  (3 * W ^ 2 - 16 * t) / 8 = (3 / 8 : Real) * (W ^ 2 - kappaFKIsing * t) := by
-- proof
  apply StatMech.SLE.fkIsingObservableJet_secondCoeff t W

/--
[fkIsingObservableJet_sq_mul_denominator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/FKIsingDrivingReduction.lean)
-/
@[path]
private lemma fkIsingObservableJet_sq_mul_denominator_eq
  {t W u : Real} :
-- imply
  let a := W / 2 let b := (3 * W ^ 2 - 16 * t) / 8 let remainder := (2 * a * b - W * (a ^ 2 + 2 * b) + 4 * t * a) + (b ^ 2 - 2 * a * b * W + 2 * t * (a ^ 2 + 2 * b)) * u + (-W * b ^ 2 + 4 * t * a * b) * u ^ 2 + (2 * t * b ^ 2) * u ^ 3 fkIsingObservableJet t W u ^ 2 * (1 - W * u + 2 * t * u ^ 2) = 1 - 2 * t * u ^ 2 + u ^ 3 * remainder := by
-- proof
  apply StatMech.SLE.fkIsingObservableJet_sq_mul_denominator t W u

/--
[kappaFKIsing_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/FKIsingDrivingReduction.lean)
-/
@[path]
private lemma kappaFKIsing_pos_eq :
-- imply
  0 < kappaFKIsing := by
-- proof
  apply StatMech.SLE.kappaFKIsing_pos

/--
[sq_sqrt_kappaFKIsing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/FKIsingDrivingReduction.lean)
-/
@[path]
private lemma sq_sqrt_kappaFKIsing_eq :
-- imply
  Real.sqrt kappaFKIsing ^ 2 = kappaFKIsing := by
-- proof
  apply StatMech.SLE.sq_sqrt_kappaFKIsing

/--
[sqrt_kappaFKIsing_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/FKIsingDrivingReduction.lean)
-/
@[path]
private lemma sqrt_kappaFKIsing_ne_zero_eq :
-- imply
  Real.sqrt kappaFKIsing ≠ 0 := by
-- proof
  apply StatMech.SLE.sqrt_kappaFKIsing_ne_zero

/--
[fkIsingDriving_div_sqrt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/FKIsingDrivingReduction.lean)
-/
@[path]
private lemma fkIsingDriving_div_sqrt_eq
  {B : Real → Omega → Real}
  {omega : Omega}
  {t : Real} :
-- imply
  sleDriving kappaFKIsing B omega t / Real.sqrt kappaFKIsing = B t omega := by
-- proof
  apply StatMech.SLE.fkIsingDriving_div_sqrt B omega t

/--
[isChordalSLE_kappaFKIsing_of_brownian_loewner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/FKIsingDrivingReduction.lean)
-/
@[path]
private lemma isChordalSLE_kappaFKIsing_of_brownian_loewner_eq
  [MeasurableSpace Omega]
  {B : Real → Omega → Real}
  {P : Measure Omega}
  {D : Omega → Real → Set ℂ}
  {g : Omega → Real → ℂ → ℂ}
-- given
  (hB : IsStandardBrownianMotion B P)
  (hloewner : ∀ᵐ omega ∂P, SatisfiesMaximalLoewnerEquation (sleDriving kappaFKIsing B omega) (D omega) (g omega)) :
-- imply
  IsChordalSLE kappaFKIsing B P D g where kappa_nonneg := by
-- proof
  apply StatMech.SLE.isChordalSLE_kappaFKIsing_of_brownian_loewner B P D g hB hloewner

/--
[isChordalSLE_kappaFKIsing_of_canonicalBrownian_loewner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/FKIsingDrivingReduction.lean)
-/
@[path]
private lemma isChordalSLE_kappaFKIsing_of_canonicalBrownian_loewner_eq
-- given
  (D : (Real -> Real) -> Real -> Set ℂ)
  (g : (Real -> Real) -> Real -> ℂ -> ℂ)
  (hloewner : ∀ᵐ omega ∂brownianProductLaw, SatisfiesMaximalLoewnerEquation (sleDriving kappaFKIsing brownianContinuousModification omega) (D omega) (g omega)) :
-- imply
  IsChordalSLE kappaFKIsing brownianContinuousModification brownianProductLaw D g := by
-- proof
  apply StatMech.SLE.isChordalSLE_kappaFKIsing_of_canonicalBrownian_loewner D g hloewner

/--
[isChordalSLE_kappaFKIsing_of_canonical_loewner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/FKIsingDrivingReduction.lean)
-/
@[path]
private lemma isChordalSLE_kappaFKIsing_of_canonical_loewner_eq :
-- imply
  IsChordalSLE kappaFKIsing brownianContinuousModification brownianProductLaw (fun omega => loewnerUnswallowedDomain (sleDriving kappaFKIsing brownianContinuousModification omega)) (fun omega => loewnerMaximalMaps (sleDriving kappaFKIsing brownianContinuousModification omega)) := by
-- proof
  apply StatMech.SLE.isChordalSLE_kappaFKIsing_of_canonical_loewner

/--
[IsChordalSLE.driving_processLaw_eq_canonicalScaled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/FKIsingDrivingReduction.lean)
-/
@[path]
private lemma driving_processLaw_eq_canonicalScaled_eq
  [MeasurableSpace Omega]
  {kappa : Real}
  {B : Real -> Omega -> Real}
  {P : Measure Omega}
  {D : Omega -> Real -> Set Complex}
  {g : Omega -> Real -> Complex -> Complex}
-- given
  (hSLE : IsChordalSLE kappa B P D g) :
-- imply
  P.map (fun omega => sleDriving kappa B omega) = brownianProductLaw.map (fun b : Real -> Real => fun t => Real.sqrt kappa * b t) := by
-- proof
  apply StatMech.SLE.IsChordalSLE.driving_processLaw_eq_canonicalScaled hSLE

/--
[tendsto_fkIsing_sleDriving_processLaw_of_isChordalSLE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/FKIsingDrivingReduction.lean)
-/
@[path]
private lemma tendsto_fkIsing_sleDriving_processLaw_of_isChordalSLE_eq
  [MeasurableSpace Omega]
-- given
  (B : Nat -> Real -> Omega -> Real)
  (P : Nat -> Measure Omega)
  (D : Nat -> Omega -> Real -> Set Complex)
  (g : Nat -> Omega -> Real -> Complex -> Complex)
  (hSLE : forall n, IsChordalSLE kappaFKIsing (B n) (P n) (D n) (g n)) :
-- imply
  Tendsto (fun n => (P n).map (fun omega => sleDriving kappaFKIsing (B n) omega)) atTop (pure (brownianProductLaw.map (fun b : Real -> Real => fun t => Real.sqrt kappaFKIsing * b t))) := by
-- proof
  apply StatMech.SLE.tendsto_fkIsing_sleDriving_processLaw_of_isChordalSLE B P D g hSLE


-- created on 2026-10-23

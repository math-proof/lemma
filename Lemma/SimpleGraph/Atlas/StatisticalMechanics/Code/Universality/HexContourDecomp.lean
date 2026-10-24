import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HexContourDecomp
open StatMech StatMech.Universality StatMech.Universality.HexSide StatMech.Universality.HexBoundaryDecomp


/--
[incSum_eq_dir_mul_fSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexContourDecomp.lean)
-/
@[path]
private lemma incSum_eq_dir_mul_fSum_eq
  [DecidableEq V]
  {D : HexDomain V}
  {s : HexSide D} :
-- imply
  s.incSum = s.dir * s.fSum := by
-- proof
  apply StatMech.Universality.HexSide.incSum_eq_dir_mul_fSum s

/--
[proj_of_tilt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexContourDecomp.lean)
-/
@[path]
private lemma proj_of_tilt_eq
  [DecidableEq V]
  {D : HexDomain V}
  {θ : ℝ}
  {c : ℂ} :
-- imply
  (Complex.I * Complex.exp ((-θ : ℝ) * Complex.I)) * (Complex.exp ((θ : ℝ) * Complex.I) * ((Real.cos θ : ℂ) * c)) = Complex.I * ((Real.cos θ : ℂ) * c) := by
-- proof
  apply StatMech.Universality.HexSide.proj_of_tilt θ c

/--
[boundarySum_eq_sum_sides](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexContourDecomp.lean)
-/
@[path]
private lemma boundarySum_eq_sum_sides_eq
  [DecidableEq V]
  {D : HexDomain V}
  {P : D.InteriorPairing} :
-- imply
  D.boundarySum P = B.A.incSum + B.L.incSum + B.Tp.incSum + B.Tm.incSum + B.U.incSum := by
-- proof
  apply StatMech.Universality.HexBoundaryDecomp.boundarySum_eq_sum_sides

/--
[boundarySum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexContourDecomp.lean)
-/
@[path]
private lemma boundarySum_eq_eq
  [DecidableEq V]
  {D : HexDomain V}
  {P : D.InteriorPairing} :
-- imply
  D.boundarySum P = Complex.I * (((hexBdryCl * B.lam + hexBdryCt * (B.taup + B.taum) + B.ups : ℝ) - (B.Fa : ℝ)) : ℂ) := by
-- proof
  apply StatMech.Universality.HexBoundaryDecomp.boundarySum_eq

/--
[hexBoundary_identity_via_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexContourDecomp.lean)
-/
@[path]
private lemma hexBoundary_identity_via_decomp_eq
  [DecidableEq V]
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {B : HexBoundaryDecomp D P}
-- given
  (hsub : P.interior ⊆ D.incidences)
  (hFa : B.Fa = 1) :
-- imply
  hexBdryCl * B.lam + hexBdryCt * (B.taup + B.taum) + B.ups = 1 := by
-- proof
  apply StatMech.Universality.hexBoundary_identity_via_decomp D P hsub B hFa

/--
[hexBoundary_identity_scales_via_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexContourDecomp.lean)
-/
@[path]
private lemma hexBoundary_identity_scales_via_decomp_eq
  [DecidableEq V]
  {D : ℕ → HexDomain V}
-- given
  (P : ∀ v, (D v).InteriorPairing)
  (hsub : ∀ v, (P v).interior ⊆ (D v).incidences)
  (B : ∀ v, HexBoundaryDecomp (D v) (P v))
  (hFa : ∀ v, 1 ≤ v → (B v).Fa = 1) :
-- imply
  ∀ v, 1 ≤ v → hexBdryCl * (B v).lam + hexBdryCt * ((B v).taup + (B v).taum) + (B v).ups = 1 := by
-- proof
  apply StatMech.Universality.hexBoundary_identity_scales_via_decomp D P hsub B hFa

/--
[hexDecomp_hdecomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexContourDecomp.lean)
-/
@[path]
private lemma hexDecomp_hdecomp_eq
  [DecidableEq V]
  {D : ℕ → HexDomain V}
-- given
  (P : ∀ v, (D v).InteriorPairing)
  (B : ∀ v, HexBoundaryDecomp (D v) (P v)) :
-- imply
  ∀ v, 1 ≤ v → (D v).boundarySum (P v) = Complex.I * ((hexBdryCl * (B v).lam + hexBdryCt * ((B v).taup + (B v).taum) + (B v).ups : ℝ) - ((B v).Fa : ℝ)) := by
-- proof
  apply StatMech.Universality.hexDecomp_hdecomp D P B

/--
[hexDecomp_projL_realize](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexContourDecomp.lean)
-/
@[path]
private lemma hexDecomp_projL_realize_eq
  {c : ℂ} :
-- imply
  (Complex.I * Complex.exp ((-(3 * Real.pi / 8) : ℝ) * Complex.I)) * (Complex.exp ((3 * Real.pi / 8 : ℝ) * Complex.I) * ((hexBdryCl : ℂ) * c)) = Complex.I * ((hexBdryCl : ℂ) * c) := by
-- proof
  apply StatMech.Universality.hexDecomp_projL_realize c

/--
[hexDecomp_projT_realize](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexContourDecomp.lean)
-/
@[path]
private lemma hexDecomp_projT_realize_eq
  {c : ℂ} :
-- imply
  (Complex.I * Complex.exp ((-(Real.pi / 4) : ℝ) * Complex.I)) * (Complex.exp ((Real.pi / 4 : ℝ) * Complex.I) * ((hexBdryCt : ℂ) * c)) = Complex.I * ((hexBdryCt : ℂ) * c) := by
-- proof
  apply StatMech.Universality.hexDecomp_projT_realize c

/--
[hexDecomp_projU_realize](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexContourDecomp.lean)
-/
@[path]
private lemma hexDecomp_projU_realize_eq
  {c : ℂ} :
-- imply
  (Complex.I * Complex.exp ((-(0 : ℝ)) * Complex.I)) * (Complex.exp ((0 : ℝ) * Complex.I) * ((1 : ℂ) * c)) = Complex.I * c := by
-- proof
  apply StatMech.Universality.hexDecomp_projU_realize c


-- created on 2026-10-23

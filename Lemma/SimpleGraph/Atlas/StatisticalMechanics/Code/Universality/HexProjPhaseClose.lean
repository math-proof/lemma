import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexProjPhaseClose.Part3
open StatMech StatMech.Universality StatMech.Universality.hpp_BoundaryIntegralData


/--
[hpp_slantEps_fold](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexProjPhaseClose.lean)
-/
@[path]
private lemma hpp_slantEps_fold_eq :
-- imply
  (1/2 : ℂ) * hexUnit 3 * Complex.exp ((-(hbi_sigma * (2*Real.pi/3)) : ℝ) * Complex.I) = (1/2 : ℂ) * Complex.exp ((3*Real.pi/4 : ℝ) * Complex.I) := by
-- proof
  apply StatMech.Universality.hpp_slantEps_fold

/--
[hpp_slantEpsBar_fold](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexProjPhaseClose.lean)
-/
@[path]
private lemma hpp_slantEpsBar_fold_eq :
-- imply
  (1/2 : ℂ) * hexUnit (-1) * Complex.exp ((hbi_sigma * (2*Real.pi/3) : ℝ) * Complex.I) = (1/2 : ℂ) * Complex.exp ((Real.pi/4 : ℝ) * Complex.I) := by
-- proof
  apply StatMech.Universality.hpp_slantEpsBar_fold

/--
[hpp_slant_madeReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexProjPhaseClose.lean)
-/
@[path]
private lemma hpp_slant_madeReal_eq :
-- imply
  (1/2 : ℂ) * Complex.exp ((3*Real.pi/4 : ℝ) * Complex.I) + (1/2 : ℂ) * Complex.exp ((Real.pi/4 : ℝ) * Complex.I) = Complex.I * ((hexBdryCt : ℝ) : ℂ) := by
-- proof
  apply StatMech.Universality.hpp_slant_madeReal

/--
[hpp_slantProj_combined](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexProjPhaseClose.lean)
-/
@[path]
private lemma hpp_slantProj_combined_eq
  {E : ℝ} :
-- imply
  (1/2 : ℂ) * hexUnit 3 * (Complex.exp ((-(hbi_sigma * (2*Real.pi/3)) : ℝ) * Complex.I) * ((E/2 : ℝ) : ℂ)) + (1/2 : ℂ) * hexUnit (-1) * (Complex.exp ((hbi_sigma * (2*Real.pi/3) : ℝ) * Complex.I) * ((E/2 : ℝ) : ℂ)) = Complex.I * ((hexBdryCt * (E/2) : ℝ) : ℂ) := by
-- proof
  apply StatMech.Universality.hpp_slantProj_combined E

/--
[hpp_singleSlantProj_re_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexProjPhaseClose.lean)
-/
@[path]
private lemma hpp_singleSlantProj_re_ne_zero_eq
  {r : ℝ}
-- given
  (hr : 0 < r) :
-- imply
  ((1/2 : ℂ) * hexUnit 3 * (Complex.exp ((-(hbi_sigma * (2*Real.pi/3)) : ℝ) * Complex.I) * (r:ℂ))).re ≠ 0 := by
-- proof
  apply StatMech.Universality.hpp_singleSlantProj_re_ne_zero r hr

/--
[hpp_alphaDir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexProjPhaseClose.lean)
-/
@[path]
private lemma hpp_alphaDir_eq :
-- imply
  (1/2 : ℂ) * hexUnit 4 = -(Complex.I / 2) := by
-- proof
  apply StatMech.Universality.hpp_alphaDir

/--
[hpp_topDir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexProjPhaseClose.lean)
-/
@[path]
private lemma hpp_topDir_eq :
-- imply
  (1/2 : ℂ) * hexUnit 1 = Complex.I / 2 := by
-- proof
  apply StatMech.Universality.hpp_topDir

/--
[hpp_alphaProj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexProjPhaseClose.lean)
-/
@[path]
private lemma hpp_alphaProj_eq
  {A : ℝ} :
-- imply
  (1/2 : ℂ) * hexUnit 4 * (((1 - hexBdryCl * A : ℝ)) : ℂ) = Complex.I * ((-(1 - hexBdryCl * A)/2 : ℝ) : ℂ) := by
-- proof
  apply StatMech.Universality.hpp_alphaProj A

/--
[hpp_topProj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexProjPhaseClose.lean)
-/
@[path]
private lemma hpp_topProj_eq
  {B : ℝ} :
-- imply
  (1/2 : ℂ) * hexUnit 1 * ((B : ℝ) : ℂ) = Complex.I * ((B/2 : ℝ) : ℂ) := by
-- proof
  apply StatMech.Universality.hpp_topProj B

/--
[boundaryIntegral_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexProjPhaseClose.lean)
-/
@[path]
private lemma boundaryIntegral_eq_eq
  {D : hpp_BoundaryIntegralData} :
-- imply
  (1/2 : ℂ) * hexUnit 4 * D.alphaFSum + (1/2 : ℂ) * hexUnit 1 * D.betaFSum + ((1/2 : ℂ) * hexUnit 3 * D.epsFSum + (1/2 : ℂ) * hexUnit (-1) * D.epsbarFSum) = Complex.I * ((((hexBdryCl * D.A + hexBdryCt * D.E + D.B : ℝ) - (D.Fa : ℝ))/2 : ℝ) : ℂ) := by
-- proof
  apply StatMech.Universality.hpp_BoundaryIntegralData.boundaryIntegral_eq D

/--
[boundaryIdentity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexProjPhaseClose.lean)
-/
@[path]
private lemma boundaryIdentity_eq
  {D : hpp_BoundaryIntegralData}
-- given
  (hFa : D.Fa = 1)
  (hvanish : (1/2 : ℂ) * hexUnit 4 * D.alphaFSum + (1/2 : ℂ) * hexUnit 1 * D.betaFSum + ((1/2 : ℂ) * hexUnit 3 * D.epsFSum + (1/2 : ℂ) * hexUnit (-1) * D.epsbarFSum) = 0) :
-- imply
  hexBdryCl * D.A + hexBdryCt * D.E + D.B = 1 := by
-- proof
  apply StatMech.Universality.hpp_BoundaryIntegralData.boundaryIdentity D hFa hvanish

/--
[hpp_hbdry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexProjPhaseClose.lean)
-/
@[path]
private lemma hpp_hbdry_eq
  {D : ℕ → hpp_BoundaryIntegralData}
-- given
  (hFa : ∀ v, 1 ≤ v → (D v).Fa = 1)
  (hvanish : ∀ v, 1 ≤ v → (1/2 : ℂ) * hexUnit 4 * (D v).alphaFSum + (1/2 : ℂ) * hexUnit 1 * (D v).betaFSum + ((1/2 : ℂ) * hexUnit 3 * (D v).epsFSum + (1/2 : ℂ) * hexUnit (-1) * (D v).epsbarFSum) = 0) :
-- imply
  ∀ v, 1 ≤ v → hexBdryCl * (D v).A + hexBdryCt * (D v).E + (D v).B = 1 := by
-- proof
  apply StatMech.Universality.hpp_hbdry D hFa hvanish

/--
[hpp_witness_vanish](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexProjPhaseClose.lean)
-/
@[path]
private lemma hpp_witness_vanish_eq :
-- imply
  (1/2 : ℂ) * hexUnit 4 * hpp_witness.alphaFSum + (1/2 : ℂ) * hexUnit 1 * hpp_witness.betaFSum + ((1/2 : ℂ) * hexUnit 3 * hpp_witness.epsFSum + (1/2 : ℂ) * hexUnit (-1) * hpp_witness.epsbarFSum) = 0 := by
-- proof
  apply StatMech.Universality.hpp_witness_vanish

/--
[hpp_witness_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexProjPhaseClose.lean)
-/
@[path]
private lemma hpp_witness_identity_eq :
-- imply
  hexBdryCl * hpp_witness.A + hexBdryCt * hpp_witness.E + hpp_witness.B = 1 := by
-- proof
  apply StatMech.Universality.hpp_witness_identity


-- created on 2026-10-23

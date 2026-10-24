import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HexBoundary
open StatMech StatMech.Universality StatMech.Universality.HexDomain


/--
[hexBdryCl_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundary.lean)
-/
@[path]
private lemma hexBdryCl_pos_eq :
-- imply
  0 < hexBdryCl := by
-- proof
  apply StatMech.Universality.hexBdryCl_pos

/--
[hexBdryCt_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundary.lean)
-/
@[path]
private lemma hexBdryCt_pos_eq :
-- imply
  0 < hexBdryCt := by
-- proof
  apply StatMech.Universality.hexBdryCt_pos

/--
[hexBdryCl_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundary.lean)
-/
@[path]
private lemma hexBdryCl_eq_eq :
-- imply
  hexBdryCl = Real.cos (3 * Real.pi / 8) := by
-- proof
  apply StatMech.Universality.hexBdryCl_eq

/--
[hexBdryCt_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundary.lean)
-/
@[path]
private lemma hexBdryCt_eq_eq :
-- imply
  hexBdryCt = Real.cos (Real.pi / 4) := by
-- proof
  apply StatMech.Universality.hexBdryCt_eq

/--
[globalSum_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundary.lean)
-/
@[path]
private lemma globalSum_eq_zero_eq
  [DecidableEq V]
  {D : HexDomain V} :
-- imply
  D.globalSum = 0 := by
-- proof
  apply StatMech.Universality.HexDomain.globalSum_eq_zero D

/--
[interior_sum_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundary.lean)
-/
@[path]
private lemma interior_sum_zero_eq
  [DecidableEq V]
  {D : HexDomain V}
  {P : D.InteriorPairing} :
-- imply
  ∑ e ∈ P.interior, D.incTerm e = 0 := by
-- proof
  apply StatMech.Universality.HexDomain.interior_sum_zero D P

/--
[globalSum_eq_incidences_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundary.lean)
-/
@[path]
private lemma globalSum_eq_incidences_sum_eq
  [DecidableEq V]
  {D : HexDomain V}
  {P : D.InteriorPairing}
-- given
  (hsub : P.interior ⊆ D.incidences) :
-- imply
  ∑ e ∈ D.incidences, D.incTerm e = (∑ e ∈ P.interior, D.incTerm e) + D.boundarySum P := by
-- proof
  apply StatMech.Universality.HexDomain.globalSum_eq_incidences_sum D P hsub

/--
[globalSum_eq_sum_incidences](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundary.lean)
-/
@[path]
private lemma globalSum_eq_sum_incidences_eq
  [DecidableEq V]
  {D : HexDomain V} :
-- imply
  D.globalSum = ∑ e ∈ D.incidences, D.incTerm e := by
-- proof
  apply StatMech.Universality.HexDomain.globalSum_eq_sum_incidences D

/--
[hexBoundaryRaw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundary.lean)
-/
@[path]
private lemma hexBoundaryRaw_eq
  [DecidableEq V]
  {D : HexDomain V}
  {P : D.InteriorPairing}
-- given
  (hsub : P.interior ⊆ D.incidences) :
-- imply
  D.boundarySum P = 0 := by
-- proof
  apply StatMech.Universality.HexDomain.hexBoundaryRaw D P hsub

/--
[hexBoundary_of_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundary.lean)
-/
@[path]
private lemma hexBoundary_of_decomp_eq
  {lam tau ups Fa : ℝ}
  {raw : ℂ}
-- given
  (hraw : raw = 0)
  (hFa : Fa = 1)
  (hdecomp : raw = Complex.I * ((hexBdryCl * lam + hexBdryCt * tau + ups : ℝ) - (Fa : ℝ))) :
-- imply
  hexBdryCl * lam + hexBdryCt * tau + ups = 1 := by
-- proof
  apply StatMech.Universality.hexBoundary_of_decomp lam tau ups Fa raw hraw hFa hdecomp

/--
[hexBoundary_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundary.lean)
-/
@[path]
private lemma hexBoundary_identity_eq
  {lam tau ups : ℕ → ℝ}
  {Fa : ℕ → ℝ}
  {raw : ℕ → ℂ}
-- given
  (hraw : ∀ v, 1 ≤ v → raw v = 0)
  (hFa : ∀ v, 1 ≤ v → Fa v = 1)
  (hdecomp : ∀ v, 1 ≤ v → raw v = Complex.I * ((hexBdryCl * lam v + hexBdryCt * tau v + ups v : ℝ) - (Fa v : ℝ))) :
-- imply
  ∀ v, 1 ≤ v → hexBdryCl * lam v + hexBdryCt * tau v + ups v = 1 := by
-- proof
  apply StatMech.Universality.hexBoundary_identity lam tau ups Fa raw hraw hFa hdecomp

/--
[hexBoundary_identity_of_domains](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundary.lean)
-/
@[path]
private lemma hexBoundary_identity_of_domains_eq
  [DecidableEq V]
  {D : ℕ → HexDomain V}
  {lam tau ups Fa : ℕ → ℝ}
-- given
  (P : ∀ v, (D v).InteriorPairing)
  (hsub : ∀ v, (P v).interior ⊆ (D v).incidences)
  (hFa : ∀ v, 1 ≤ v → Fa v = 1)
  (hdecomp : ∀ v, 1 ≤ v → (D v).boundarySum (P v) = Complex.I * ((hexBdryCl * lam v + hexBdryCt * tau v + ups v : ℝ) - (Fa v : ℝ))) :
-- imply
  ∀ v, 1 ≤ v → hexBdryCl * lam v + hexBdryCt * tau v + ups v = 1 := by
-- proof
  apply StatMech.Universality.hexBoundary_identity_of_domains D P hsub lam tau ups Fa hFa hdecomp

/--
[hexContour_tendsto_of_monotone_bdd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundary.lean)
-/
@[path]
private lemma hexContour_tendsto_of_monotone_bdd_eq
  {f : ℕ → ℝ}
  {B : ℝ}
-- given
  (hmono : Monotone f)
  (hbdd : ∀ n, f n ≤ B) :
-- imply
  ∃ L : ℝ, Tendsto f atTop (𝓝 L) := by
-- proof
  apply StatMech.Universality.hexContour_tendsto_of_monotone_bdd f B hmono hbdd

/--
[hexContour_limits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundary.lean)
-/
@[path]
private lemma hexContour_limits_eq
  {lam tau ups : ℕ → ℝ}
-- given
  (hbdry : ∀ h, hexBdryCl * lam h + hexBdryCt * tau h + ups h = 1)
  (hlamMono : Monotone lam)
  (hupsMono : Monotone ups)
  (hlamNN : ∀ h, 0 ≤ lam h)
  (hupsNN : ∀ h, 0 ≤ ups h)
  (htauNN : ∀ h, 0 ≤ tau h) :
-- imply
  ∃ Llam Ltau Lups : ℝ, Tendsto lam atTop (𝓝 Llam) ∧ Tendsto tau atTop (𝓝 Ltau) ∧ Tendsto ups atTop (𝓝 Lups) ∧ hexBdryCl * Llam + hexBdryCt * Ltau + Lups = 1 := by
-- proof
  apply StatMech.Universality.hexContour_limits lam tau ups hbdry hlamMono hupsMono hlamNN hupsNN htauNN


-- created on 2026-10-23

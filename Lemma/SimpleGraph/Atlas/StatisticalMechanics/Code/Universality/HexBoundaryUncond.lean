import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HexBoundaryUncond
open StatMech StatMech.Universality


/--
[hexUncondDomain_interiorVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryUncond.lean)
-/
@[path]
private lemma hexUncondDomain_interiorVertices_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  (hexUncondDomain a h0).interiorVertices = {0} := by
-- proof
  apply StatMech.Universality.hexUncondDomain_interiorVertices a h0

/--
[hexUncond_interior_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryUncond.lean)
-/
@[path]
private lemma hexUncond_interior_sub_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  (hexUncondPairing a h0).interior ⊆ (hexUncondDomain a h0).incidences := by
-- proof
  apply StatMech.Universality.hexUncond_interior_sub a h0

/--
[hexUncond_raw_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryUncond.lean)
-/
@[path]
private lemma hexUncond_raw_eq_zero_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  (hexUncondDomain a h0).boundarySum (hexUncondPairing a h0) = 0 := by
-- proof
  apply StatMech.Universality.hexUncond_raw_eq_zero a h0

/--
[hexBoundary_identity_uncond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryUncond.lean)
-/
@[path]
private lemma hexBoundary_identity_uncond_eq
  {a : ℂ}
  {lam tau ups Fa : ℝ}
-- given
  (h0 : ℤ)
  (hFa : Fa = 1)
  (hdecomp : (hexUncondDomain a h0).boundarySum (hexUncondPairing a h0) = Complex.I * ((hexBdryCl * lam + hexBdryCt * tau + ups : ℝ) - (Fa : ℝ))) :
-- imply
  hexBdryCl * lam + hexBdryCt * tau + ups = 1 := by
-- proof
  apply StatMech.Universality.hexBoundary_identity_uncond a h0 lam tau ups Fa hFa hdecomp

/--
[hexBoundary_identity_uncond_scales](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryUncond.lean)
-/
@[path]
private lemma hexBoundary_identity_uncond_scales_eq
  {a : ℕ → ℂ}
  {lam tau ups Fa : ℕ → ℝ}
-- given
  (h0 : ℕ → ℤ)
  (hFa : ∀ v, 1 ≤ v → Fa v = 1)
  (hdecomp : ∀ v, 1 ≤ v → (hexUncondDomain (a v) (h0 v)).boundarySum (hexUncondPairing (a v) (h0 v)) = Complex.I * ((hexBdryCl * lam v + hexBdryCt * tau v + ups v : ℝ) - (Fa v : ℝ))) :
-- imply
  ∀ v, 1 ≤ v → hexBdryCl * lam v + hexBdryCt * tau v + ups v = 1 := by
-- proof
  apply StatMech.Universality.hexBoundary_identity_uncond_scales a h0 lam tau ups Fa hFa hdecomp

/--
[hexBoundary_identity_uncond_via_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryUncond.lean)
-/
@[path]
private lemma hexBoundary_identity_uncond_via_decomp_eq
  {a : ℂ}
  {B : HexBoundaryDecomp (hexUncondDomain a h0) (hexUncondPairing a h0)}
-- given
  (h0 : ℤ)
  (hFa : B.Fa = 1) :
-- imply
  hexBdryCl * B.lam + hexBdryCt * (B.taup + B.taum) + B.ups = 1 := by
-- proof
  apply StatMech.Universality.hexBoundary_identity_uncond_via_decomp a h0 B hFa


-- created on 2026-10-23

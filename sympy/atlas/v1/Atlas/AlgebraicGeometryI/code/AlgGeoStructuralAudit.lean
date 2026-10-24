/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AlgGeoStructuralAudit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.CanonicalSheafCurves
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalSheafCurves
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.DedekindCurve
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannRochCurves
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannHurwitzFormula
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannHurwitzApplications
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.BertiniDimensionCount
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.SerreDualityCurves
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannRochRiemannForm
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.GrothendieckBirkhoffGeometric
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.ProjectiveIntersection
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.DedekindCurve
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.RiemannRochCurves
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.RiemannHurwitzFormula
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.RiemannHurwitzApplications
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.BertiniDimensionCount
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.SerreDualityCurves
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.RiemannRochRiemannForm
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.GrothendieckBirkhoffGeometric
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.ProjectiveIntersection
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.GAGA

noncomputable section

open CanonicalSheafCurves RiemannRochCurves


example : (mkCurve 0).g = 0 := rfl
example : (mkCurve 3).g = 3 := rfl
example : 0 ≤ (mkCurve 5).g := (mkCurve 5).hg_nonneg

#check @RiemannRochRiemannForm.SerreDualityCurve


example (C : SmoothCompleteCurve) : SerreDualityCurves.LocallyFreeSheaf C :=
  ⟨0, 42⟩


#check @GBGeometric.P1VectorBundle

#check @RiemannHurwitzFormula.CurveMorphismData


example : RiemannHurwitzFormula.CurveMorphismData where
  degree := 1
  deg_KX := 999
  deg_KY := 0
  deg_R := 0
  h_deg_R_nonneg := le_refl 0
  h_deg_pos := by norm_num


#check @HasSerreDimensionInequality

#check @DedekindCurve.eulerCharO_eq

example (k : Type*) [Field k] (C : DedekindCurve k) :
    C.eulerCharO = 1 - (C.ddGenus : ℤ) := rfl

#check @DedekindCurve.degK_eq_2g_sub_2

example (k : Type*) [Field k] (C : DedekindCurve k) :
    C.degK = 2 * (C.ddGenus : ℤ) - 2 := rfl

#check @DedekindCurve.h1_O_eq_genus
#check @DedekindCurve.h1_sky_eq_zero

#check @bertini_projective_chevalley_gap

#check @SmoothCompleteCurve.hχ_canonical

#check @RiemannRochRiemannForm.SerreDualityCurve.serre_dual

#check @RiemannHurwitzFormula.riemann_hurwitz_canonical_decomp

#check @RiemannHurwitzFormula.riemann_hurwitz_degree_corollary


#check @RiemannHurwitzApplications.luroth_theorem_target_genus_zero

#check CanonicalSheafCurves.adjunction_genus_plane_curve

example (d : ℤ) : d * (d - 3) + 2 = (d - 1) * (d - 2) := by ring

#check CanonicalSheafCurves.chi_eq_rr


#check @RiemannHurwitzFormula.ellipticCurveP1Data

#check @SmoothSubvariety


example (C : SmoothCompleteCurve) : SerreDualityCurves.LocallyFreeSheaf C :=
  ⟨0, -100⟩

#check CanonicalSheafCurves.adjunction_genus_plane_curve_degK

#check @RiemannHurwitzFormula.CurveMorphismData

#check @CanonicalSheafCurves.deg_canonical_eq_2g_sub_2
#check @DedekindCurve.degK_eq_2g_sub_2

#check @CanonicalSheafCurves.chi_eq_rr
#check @DedekindCurve.cohChi_eq_rrHom

#check @CanonicalSheafCurves.curveWitness_of_nat

#check @GAGA.gaga_pic0_is_complex_torus

#check @DedekindCurve.h1_O_sheaf_eq_genus
#check @DedekindCurve.eulerCharO_sheaf_eq_formula
#check @DedekindCurve.degK_sheaf_eq_formula


end

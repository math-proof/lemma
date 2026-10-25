/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVariational.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEquations.Part7
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheVariational.Part3
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem hasFDerivAt_sixVertexTheta {c : ℝ} (hc : 2 < c) (x y : ℝ) :
    HasFDerivAt (fun xy : ℝ × ℝ => sixVertexTheta c xy.1 xy.2)
      (sixVertexThetaFDeriv c x y) (x, y) := by
  let fx : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
  let fy : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
  have hx : HasFDerivAt (fun xy : ℝ × ℝ => xy.1) fx (x, y) := fx.hasFDerivAt
  have hy : HasFDerivAt (fun xy : ℝ × ℝ => xy.2) fy (x, y) := fy.hasFDerivAt
  have hsinx : HasFDerivAt (fun xy : ℝ × ℝ => Real.sin xy.1)
      ((Real.cos x) • fx) (x, y) := by
    simpa using (Real.hasDerivAt_sin x).comp_hasFDerivAt (x, y) hx
  have hsiny : HasFDerivAt (fun xy : ℝ × ℝ => Real.sin xy.2)
      ((Real.cos y) • fy) (x, y) := by
    simpa using (Real.hasDerivAt_sin y).comp_hasFDerivAt (x, y) hy
  have hcosx : HasFDerivAt (fun xy : ℝ × ℝ => Real.cos xy.1)
      ((-Real.sin x) • fx) (x, y) := by
    have h := (Real.hasDerivAt_cos x).comp_hasFDerivAt (x, y) hx
    convert h using 1
  have hcosy : HasFDerivAt (fun xy : ℝ × ℝ => Real.cos xy.2)
      ((-Real.sin y) • fy) (x, y) := by
    have h := (Real.hasDerivAt_cos y).comp_hasFDerivAt (x, y) hy
    convert h using 1
  have hnum := hsinx.sub hsiny
  have hden := (hcosx.add hcosy).sub_const (2 * sixVertexDelta c)
  have hden0 : sixVertexThetaDenominator c x y ≠ 0 :=
    (sixVertexThetaDenominator_pos hc x y).ne'
  have hinv := (hasFDerivAt_inv hden0).comp (x, y) hden
  have hratio := hnum.mul hinv
  have harctan := hratio.arctan
  have htheta := (hy.sub hx).add (harctan.const_mul 2)
  let g : ℝ × ℝ → ℝ := fun xy => sixVertexTheta c xy.1 xy.2
  have hgdiff : DifferentiableAt ℝ g (x, y) := by
    dsimp [g, sixVertexTheta]
    simpa only [div_eq_mul_inv] using htheta.differentiableAt
  have hg := hgdiff.hasFDerivAt
  have hlineLeft : HasDerivAt (fun t => g (t, y))
      (fderiv ℝ g (x, y) (1, 0)) x := by
    have hpath := (hasDerivAt_id x).prodMk (hasDerivAt_const x y)
    simpa [Function.comp_def] using hg.comp_hasDerivAt x hpath
  have hlineRight : HasDerivAt (fun t => g (x, t))
      (fderiv ℝ g (x, y) (0, 1)) y := by
    have hpath := (hasDerivAt_const y x).prodMk (hasDerivAt_id y)
    simpa [Function.comp_def] using hg.comp_hasDerivAt y hpath
  have hleft : fderiv ℝ g (x, y) (1, 0) =
      4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c y /
        sixVertexThetaDerivativeDenominator c x y := by
    apply hlineLeft.unique
    simpa [g, sixVertexBetheIntegratingFactor,
      sixVertexThetaDerivativeDenominator] using
        hasDerivAt_sixVertexTheta_left hc x y
  have hright : fderiv ℝ g (x, y) (0, 1) =
      -4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c x /
        sixVertexThetaDerivativeDenominator c x y := by
    apply hlineRight.unique
    simpa [g] using hasDerivAt_sixVertexTheta_right hc x y
  have hmap : fderiv ℝ g (x, y) = sixVertexThetaFDeriv c x y := by
    apply ContinuousLinearMap.ext
    rintro ⟨u, v⟩
    have hdecomp : (u, v) = u • (1, 0) + v • (0, 1) := by
      ext <;> simp
    rw [hdecomp, map_add, map_smul, map_smul, hleft, hright]
    simp [sixVertexThetaFDeriv]
  rw [← hmap]
  exact hg


end
end StatMech.FrontierD

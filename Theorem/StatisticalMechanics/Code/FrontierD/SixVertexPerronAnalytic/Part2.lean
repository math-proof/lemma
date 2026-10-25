/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronAnalytic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheVandermonde.Part5
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPerronAnalytic
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexSectorCharacteristicDet_prodMk
    (N n : Nat) (c t : Real) :
    sixVertexSectorCharacteristicDet N n (c, t) =
      (sixVertexSectorTransfer N n c).charpoly.eval t := by
  rw [Matrix.eval_charpoly]
  unfold sixVertexSectorCharacteristicDet
  congr 1
  ext i j
  simp [Matrix.one_apply, Matrix.scalar_apply, Matrix.diagonal_apply]

theorem analyticAt_sixVertexSectorCharacteristicGraph
    (N n : Nat) (q : Real × Real) :
    AnalyticAt Real (sixVertexSectorCharacteristicGraph N n) q := by
  apply analyticAt_fst.prod
  simpa only [sixVertexSectorCharacteristicDet] using
    analyticAt_sixVertexSectorCharacteristicDet N n q

theorem sixVertexSectorCharacteristicGraph_fderiv_injective
    {N n : Nat} (hn : n ≤ N) {c : Real} (hc : 0 < c) :
    Function.Injective (fderiv Real (sixVertexSectorCharacteristicGraph N n)
      (c, sixVertexSectorTopEigenvalue N n hn c)) := by
  let μ := sixVertexSectorTopEigenvalue N n hn c
  let q₀ : Real × Real := (c, μ)
  let L := fderiv Real (sixVertexSectorCharacteristicGraph N n) q₀
  let b := (sixVertexSectorTransfer N n c).charpoly.derivative.eval μ
  have hb : b ≠ 0 := sixVertexSectorTop_charpoly_derivative_ne_zero hn hc
  have hH : AnalyticAt Real (sixVertexSectorCharacteristicGraph N n) q₀ :=
    analyticAt_sixVertexSectorCharacteristicGraph N n q₀
  have hfirstDeriv : HasFDerivAt
      (fun q ↦ (sixVertexSectorCharacteristicGraph N n q).1)
      ((ContinuousLinearMap.fst Real Real Real).comp L) q₀ :=
    hH.hasStrictFDerivAt.hasFDerivAt.fst
  have hfirst : (ContinuousLinearMap.fst Real Real Real).comp L =
      ContinuousLinearMap.fst Real Real Real := by
    apply HasFDerivAt.unique hfirstDeriv
    simpa only [sixVertexSectorCharacteristicGraph] using
      (hasFDerivAt_fst (p := q₀))
  have hcurve : HasDerivAt
      (fun t : Real ↦ sixVertexSectorCharacteristicGraph N n (c, t))
      (0, b) μ := by
    apply (hasDerivAt_const μ c).prodMk
    simpa only [sixVertexSectorCharacteristicGraph,
      sixVertexSectorCharacteristicDet_prodMk, b] using
        (sixVertexSectorTransfer N n c).charpoly.hasDerivAt μ
  have hline : HasDerivAt (fun t : Real ↦ (c, t)) (0, 1) μ :=
    (hasDerivAt_const μ c).prodMk (hasDerivAt_id μ)
  have hcurve' := hH.hasStrictFDerivAt.hasFDerivAt.comp μ hline
  have hvertical : L (0, 1) = (0, b) := by
    have heq := hcurve'.unique hcurve.hasFDerivAt
    have happ := congrArg (fun K : Real →L[Real] Real × Real ↦ K 1) heq
    simpa [L, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply] using happ
  change Function.Injective L
  intro v w hvw
  apply sub_eq_zero.mp
  let z := v - w
  have hz : L z = 0 := by simp [z, hvw]
  have hLzfirst : (L z).1 = z.1 := by
    have happ := congrArg (fun K : (Real × Real) →L[Real] Real ↦ K z) hfirst
    exact happ
  have hzfirst : z.1 = 0 := by rw [← hLzfirst, hz]; rfl
  have hzdecomp : z = z.2 • ((0, 1) : Real × Real) := by
    ext <;> simp [hzfirst]
  have hzsecond : z.2 * b = 0 := by
    have hzsnd := congrArg Prod.snd hz
    rw [hzdecomp, map_smul, hvertical] at hzsnd
    simpa [mul_comm] using hzsnd
  have : z.2 = 0 := (mul_eq_zero.mp hzsecond).resolve_right hb
  exact Prod.ext hzfirst this


theorem analyticAt_sixVertexSectorTopEigenvalue
    {N n : Nat} (hn : n ≤ N) {c : Real} (hc : 0 < c) :
    AnalyticAt Real (sixVertexSectorTopEigenvalue N n hn) c := by
  let μ := sixVertexSectorTopEigenvalue N n hn c
  let q₀ : Real × Real := (c, μ)
  let H := sixVertexSectorCharacteristicGraph N n
  let L := fderiv Real H q₀
  have hH : AnalyticAt Real H q₀ :=
    analyticAt_sixVertexSectorCharacteristicGraph N n q₀
  have hLinj : Function.Injective L :=
    sixVertexSectorCharacteristicGraph_fderiv_injective hn hc
  have hker : L.ker = ⊥ := LinearMap.ker_eq_bot.mpr hLinj
  have hrange : L.range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    exact LinearMap.injective_iff_surjective.mp hLinj
  let e : (Real × Real) ≃L[Real] (Real × Real) :=
    ContinuousLinearEquiv.ofBijective L hker hrange
  have hHe : HasStrictFDerivAt H
      (e : (Real × Real) →L[Real] (Real × Real)) q₀ := by
    simpa [L, e, ContinuousLinearEquiv.coe_ofBijective] using
      hH.hasStrictFDerivAt
  let R : OpenPartialHomeomorph (Real × Real) (Real × Real) :=
    hHe.toOpenPartialHomeomorph H
  have hqsource : q₀ ∈ R.source := hHe.mem_toOpenPartialHomeomorph_source
  have hR : AnalyticAt Real R.symm (H q₀) := by
    apply R.analyticAt_symm' hqsource
    · simpa [R] using hH
    · simpa [R] using hHe.hasFDerivAt.fderiv
  have hdet0 : sixVertexSectorCharacteristicDet N n q₀ = 0 := by
    exact sixVertexSectorCharacteristicDet_top_eq_zero hn c
  have hHq₀ : H q₀ = (c, (0 : Real)) := by simp [H, q₀, μ, hdet0,
    sixVertexSectorCharacteristicGraph]
  let g : Real → Real := fun t => (R.symm (t, (0 : Real))).2
  have hg : AnalyticAt Real g c := by
    rw [hHq₀] at hR
    have hinput : AnalyticAt Real (fun t : Real => (t, (0 : Real))) c :=
      analyticAt_id.prod analyticAt_const
    have hcomp : AnalyticAt Real
        (R.symm ∘ fun t : Real => (t, (0 : Real))) c :=
      hR.comp (f := fun t : Real => (t, (0 : Real))) (x := c) hinput
    have hsnd : AnalyticAt Real
        (Prod.snd ∘ R.symm ∘ fun t : Real => (t, (0 : Real))) c :=
      analyticAt_snd.comp hcomp
    simpa only [Function.comp_apply] using hsnd
  apply hg.congr
  have htopContinuous : ContinuousAt
      (sixVertexSectorTopEigenvalue N n hn) c :=
    (continuous_sixVertexSectorTopEigenvalue hn).continuousAt
  have hgraph : Tendsto
      (fun t => (t, sixVertexSectorTopEigenvalue N n hn t))
      (𝓝 c) (𝓝 q₀) := by
    exact continuousAt_id.prodMk htopContinuous
  have hsource : ∀ᶠ t in 𝓝 c,
      (t, sixVertexSectorTopEigenvalue N n hn t) ∈ R.source :=
    hgraph.eventually (R.open_source.mem_nhds hqsource)
  filter_upwards [hsource] with t ht
  have hleft := R.left_inv ht
  have hdet := sixVertexSectorCharacteristicDet_top_eq_zero hn t
  have hdet' : sixVertexSectorCharacteristicDet N n
      (t, sixVertexSectorTopEigenvalue N n hn t) = 0 := hdet
  have hHtop : H (t, sixVertexSectorTopEigenvalue N n hn t) =
      (t, (0 : Real)) := by
    simp [H, sixVertexSectorCharacteristicGraph, hdet']
  have hinv : R.symm (t, (0 : Real)) =
      (t, sixVertexSectorTopEigenvalue N n hn t) := by
    rw [← hHtop]
    simpa [R] using hleft
  exact congrArg Prod.snd hinv

theorem analyticOnNhd_sixVertexSectorTopEigenvalue
    {N n : Nat} (hn : n ≤ N) :
    AnalyticOnNhd Real (sixVertexSectorTopEigenvalue N n hn) (Set.Ioi 0) := by
  intro c hc
  exact analyticAt_sixVertexSectorTopEigenvalue hn hc

end
end StatMech.FrontierD

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricAnalytic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricAnalytic.Part4
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddSymmetricAnalytic
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexOddSymmetricBetheResidualGraph_fderiv_injective
    {N m : Nat} {c : Real} (hc : 2 < c) {q : Fin m → Real}
    (hjac : Function.Injective
      (sixVertexOddSymmetricBetheRootJacobian N m c q)) :
    Function.Injective
      (fderiv Real (sixVertexOddSymmetricBetheResidualGraph N m) (c, q)) := by
  let H := sixVertexOddSymmetricBetheResidualGraph N m
  let L := fderiv Real H (c, q)
  let J := sixVertexOddSymmetricBetheRootJacobian N m c q
  have hH : HasFDerivAt H L (c, q) :=
    (analyticAt_sixVertexOddSymmetricBetheResidualGraph N m (c, q) hc)
      |>.hasStrictFDerivAt.hasFDerivAt
  let incl : (Fin m → Real) →L[Real] (Real × (Fin m → Real)) :=
    (0 : (Fin m → Real) →L[Real] Real).prod
      (ContinuousLinearMap.id Real (Fin m → Real))
  have hincl : HasFDerivAt (fun r : Fin m → Real => (c, r)) incl q :=
    (hasFDerivAt_const c q).prodMk (hasFDerivAt_id q)
  have hcomp : HasFDerivAt (fun r : Fin m → Real => H (c, r))
      (L.comp incl) q := hH.comp q hincl
  have hres : HasFDerivAt
      (sixVertexOddSymmetricBetheResidual N m c) J q :=
    (analyticAt_sixVertexOddSymmetricBetheResidual_family N m (c, q) hc)
      |>.comp (x := q) (f := fun r : Fin m → Real => (c, r))
        (analyticAt_const.prod analyticAt_id)
      |>.hasStrictFDerivAt.hasFDerivAt
  let direct : (Fin m → Real) →L[Real] (Real × (Fin m → Real)) :=
    (0 : (Fin m → Real) →L[Real] Real).prod J
  have hdirect : HasFDerivAt (fun r : Fin m → Real => H (c, r))
      direct q := (hasFDerivAt_const c q).prodMk hres
  have hderiv : L.comp incl = direct := hcomp.unique hdirect
  intro z w hzw
  let u := z - w
  have hu : L u = 0 := by
    dsimp [u, L]
    rw [map_sub, hzw, sub_self]
  have hfst : u.1 = 0 := by
    have hproj : HasFDerivAt
        (fun z : Real × (Fin m → Real) => z.1)
        (ContinuousLinearMap.fst Real Real (Fin m → Real)) (c, q) :=
      (ContinuousLinearMap.fst Real Real (Fin m → Real)).hasFDerivAt
    have hcompFst : HasFDerivAt
        (fun z : Real × (Fin m → Real) => z.1)
        ((ContinuousLinearMap.fst Real Real (Fin m → Real)).comp L) (c, q) := by
      simpa [H, sixVertexOddSymmetricBetheResidualGraph] using
        ((ContinuousLinearMap.fst Real Real (Fin m → Real)).hasFDerivAt.comp
          (c, q) hH)
    have hfstL :
        (ContinuousLinearMap.fst Real Real (Fin m → Real)).comp L =
          ContinuousLinearMap.fst Real Real (Fin m → Real) :=
      hcompFst.unique hproj
    have h := congrArg
      (fun T : (Real × (Fin m → Real)) →L[Real] Real => T u) hfstL
    simpa [hu] using h.symm
  have hupair : u = (0, u.2) := Prod.ext hfst rfl
  have hJzero : J u.2 = 0 := by
    have happly := congrArg
      (fun T : (Fin m → Real) →L[Real] (Real × (Fin m → Real)) => T u.2)
      hderiv
    have hLzero : L (incl u.2) = 0 := by
      rw [show incl u.2 = u by rw [hupair]; rfl]
      exact hu
    simpa [hLzero, direct] using (congrArg Prod.snd happly).symm
  have hu2 : u.2 = 0 := hjac (by simpa using hJzero)
  have hsub : z - w = 0 := by
    change u = 0
    exact Prod.ext hfst hu2
  exact sub_eq_zero.mp hsub

theorem exists_sixVertexLocalAnalyticOddSymmetricBetheBranch
    {N m : Nat} {c : Real} (hc : 2 < c) {q : Fin m → Real}
    (hsol : SixVertexSatisfiesBetheEquations c N ((m + 1) + m)
      (sixVertexOddSymmetricLift m q))
    (hjac : Function.Injective
      (sixVertexOddSymmetricBetheRootJacobian N m c q)) :
    Nonempty (SixVertexLocalAnalyticOddSymmetricBetheBranch N m c q) := by
  let q₀ : Real × (Fin m → Real) := (c, q)
  let H := sixVertexOddSymmetricBetheResidualGraph N m
  let L := fderiv Real H q₀
  have hH : AnalyticAt Real H q₀ :=
    analyticAt_sixVertexOddSymmetricBetheResidualGraph N m q₀ hc
  have hLinj : Function.Injective L :=
    sixVertexOddSymmetricBetheResidualGraph_fderiv_injective hc hjac
  have hker : L.ker = ⊥ := LinearMap.ker_eq_bot.mpr hLinj
  have hrange : L.range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    exact LinearMap.injective_iff_surjective.mp hLinj
  let e : (Real × (Fin m → Real)) ≃L[Real] (Real × (Fin m → Real)) :=
    ContinuousLinearEquiv.ofBijective L hker hrange
  have hHe : HasStrictFDerivAt H
      (e : (Real × (Fin m → Real)) →L[Real]
        (Real × (Fin m → Real))) q₀ := by
    simpa [L, e, ContinuousLinearEquiv.coe_ofBijective] using
      hH.hasStrictFDerivAt
  let R : OpenPartialHomeomorph
      (Real × (Fin m → Real)) (Real × (Fin m → Real)) :=
    hHe.toOpenPartialHomeomorph H
  have hqsource : q₀ ∈ R.source := hHe.mem_toOpenPartialHomeomorph_source
  have hzero : sixVertexOddSymmetricBetheResidual N m c q = 0 :=
    (sixVertexOddSymmetricBetheResidual_eq_zero_iff N m c q).2 hsol
  have hHq₀ : H q₀ = (c, (0 : Fin m → Real)) := by
    apply Prod.ext
    · rfl
    · simpa [H, q₀, sixVertexOddSymmetricBetheResidualGraph] using hzero
  have hR : AnalyticAt Real R.symm (H q₀) := by
    apply R.analyticAt_symm' hqsource
    · simpa [R] using hH
    · simpa [R] using hHe.hasFDerivAt.fderiv
  let roots : Real → (Fin m → Real) :=
    fun t => (R.symm (t, (0 : Fin m → Real))).2
  have hroots : AnalyticAt Real roots c := by
    rw [hHq₀] at hR
    have hinput : AnalyticAt Real
        (fun t : Real => (t, (0 : Fin m → Real))) c :=
      analyticAt_id.prod analyticAt_const
    have hcomp : AnalyticAt Real
        (R.symm ∘ fun t : Real => (t, (0 : Fin m → Real))) c :=
      hR.comp (f := fun t : Real => (t, (0 : Fin m → Real))) (x := c) hinput
    have hsnd := analyticAt_snd.comp hcomp
    simpa only [Function.comp_apply] using hsnd
  have hrootsAt : roots c = q := by
    have hleft := R.left_inv hqsource
    have hinv : R.symm (c, (0 : Fin m → Real)) = (c, q) := by
      rw [← hHq₀]
      simpa [R, q₀] using hleft
    exact congrArg Prod.snd hinv
  have hright := hHe.eventually_right_inverse
  have hinput : Tendsto (fun t : Real => (t, (0 : Fin m → Real)))
      (nhds c) (nhds (H q₀)) := by
    rw [hHq₀]
    exact continuousAt_id.prodMk continuousAt_const
  have hbranchEq : ∀ᶠ t in nhds c,
      H (R.symm (t, (0 : Fin m → Real))) =
        (t, (0 : Fin m → Real)) := hinput.eventually hright
  have hsolution : ∀ᶠ t in nhds c,
      SixVertexSatisfiesBetheEquations t N ((m + 1) + m)
        (sixVertexOddSymmetricLift m (roots t)) := by
    filter_upwards [hbranchEq] with t ht
    apply (sixVertexOddSymmetricBetheResidual_eq_zero_iff N m t (roots t)).1
    have hfst := congrArg Prod.fst ht
    have hsnd := congrArg Prod.snd ht
    change (R.symm (t, (0 : Fin m → Real))).1 = t at hfst
    change sixVertexOddSymmetricBetheResidual N m
      (R.symm (t, (0 : Fin m → Real))).1
      (R.symm (t, (0 : Fin m → Real))).2 = 0 at hsnd
    rw [hfst] at hsnd
    simpa [roots] using hsnd
  have hsource : ∀ᶠ z : Real × (Fin m → Real) in nhds q₀,
      z ∈ R.source := R.open_source.mem_nhds hqsource
  have hunique : ∀ᶠ z : Real × (Fin m → Real) in nhds q₀,
      SixVertexSatisfiesBetheEquations z.1 N ((m + 1) + m)
        (sixVertexOddSymmetricLift m z.2) → roots z.1 = z.2 := by
    filter_upwards [hsource] with z hz hzsol
    have hzres : sixVertexOddSymmetricBetheResidual N m z.1 z.2 = 0 :=
      (sixVertexOddSymmetricBetheResidual_eq_zero_iff N m z.1 z.2).2 hzsol
    have hHz : H z = (z.1, (0 : Fin m → Real)) := by
      apply Prod.ext
      · rfl
      · simpa [H, sixVertexOddSymmetricBetheResidualGraph] using hzres
    have hleft := R.left_inv hz
    have hinv : R.symm (z.1, (0 : Fin m → Real)) = z := by
      rw [← hHz]
      simpa [R] using hleft
    exact congrArg Prod.snd hinv
  exact ⟨{
    roots := roots
    analyticAt_roots := hroots
    roots_at := hrootsAt
    eventually_solution := hsolution
    eventually_unique := by simpa [q₀] using hunique
  }⟩

end
end StatMech.FrontierD

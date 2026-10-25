/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheLocalAnalytic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnalyticContinuation.Part2
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.Homotopy.Affine
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexBetheLocalAnalytic
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem exists_sixVertexLocalAnalyticBetheBranch
    {N n : Nat} {c : Real} (hc : 2 < c) {p : Fin n → Real}
    (hsol : SixVertexSatisfiesBetheEquations c N n p)
    (hjac : Function.Injective
      (fderiv Real (sixVertexBetheResidualGraph N n) (c, p))) :
    Nonempty (SixVertexLocalAnalyticBetheBranch N n c p) := by
  let q₀ : Real × (Fin n → Real) := (c, p)
  let H := sixVertexBetheResidualGraph N n
  let L := fderiv Real H q₀
  have hH : AnalyticAt Real H q₀ :=
    analyticAt_sixVertexBetheResidualGraph N n q₀ hc
  have hker : L.ker = ⊥ := LinearMap.ker_eq_bot.mpr hjac
  have hrange : L.range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    exact LinearMap.injective_iff_surjective.mp hjac
  let e : (Real × (Fin n → Real)) ≃L[Real]
      (Real × (Fin n → Real)) :=
    ContinuousLinearEquiv.ofBijective L hker hrange
  have hHe : HasStrictFDerivAt H
      (e : (Real × (Fin n → Real)) →L[Real]
        (Real × (Fin n → Real))) q₀ := by
    simpa [L, e, ContinuousLinearEquiv.coe_ofBijective] using
      hH.hasStrictFDerivAt
  let R : OpenPartialHomeomorph
      (Real × (Fin n → Real)) (Real × (Fin n → Real)) :=
    hHe.toOpenPartialHomeomorph H
  have hqsource : q₀ ∈ R.source := hHe.mem_toOpenPartialHomeomorph_source
  have hzero : (fun j => sixVertexBetheResidual c N n p j) = 0 := by
    funext j
    exact (sixVertexBetheResidual_eq_zero_iff c N n p).2 hsol j
  have hHq₀ : H q₀ = (c, (0 : Fin n → Real)) := by
    apply Prod.ext
    · rfl
    · simpa [H, q₀, sixVertexBetheResidualGraph] using hzero
  have hR : AnalyticAt Real R.symm (H q₀) := by
    apply R.analyticAt_symm' hqsource
    · simpa [R] using hH
    · simpa [R] using hHe.hasFDerivAt.fderiv
  let roots : Real → (Fin n → Real) :=
    fun t => (R.symm (t, (0 : Fin n → Real))).2
  have hroots : AnalyticAt Real roots c := by
    rw [hHq₀] at hR
    have hinput : AnalyticAt Real
        (fun t : Real => (t, (0 : Fin n → Real))) c :=
      analyticAt_id.prod analyticAt_const
    have hcomp : AnalyticAt Real
        (R.symm ∘ fun t : Real => (t, (0 : Fin n → Real))) c :=
      hR.comp (f := fun t : Real => (t, (0 : Fin n → Real)))
        (x := c) hinput
    have hsnd : AnalyticAt Real
        (Prod.snd ∘ R.symm ∘
          fun t : Real => (t, (0 : Fin n → Real))) c :=
      analyticAt_snd.comp hcomp
    simpa only [Function.comp_apply] using hsnd
  have hrootsAt : roots c = p := by
    have hleft := R.left_inv hqsource
    have hinv : R.symm (c, (0 : Fin n → Real)) = (c, p) := by
      rw [← hHq₀]
      simpa [R, q₀] using hleft
    exact congrArg Prod.snd hinv
  have hright := hHe.eventually_right_inverse
  have hinput : Tendsto
      (fun t : Real => (t, (0 : Fin n → Real)))
      (𝓝 c) (𝓝 (H q₀)) := by
    rw [hHq₀]
    exact continuousAt_id.prodMk continuousAt_const
  have hbranchEq : ∀ᶠ t in 𝓝 c,
      H (R.symm (t, (0 : Fin n → Real))) =
        (t, (0 : Fin n → Real)) :=
    hinput.eventually hright
  have hsolution : ∀ᶠ t in 𝓝 c,
      SixVertexSatisfiesBetheEquations t N n (roots t) := by
    filter_upwards [hbranchEq] with t ht
    apply (sixVertexBetheResidual_eq_zero_iff t N n (roots t)).1
    intro j
    have hfst := congrArg Prod.fst ht
    have hsnd := congrArg Prod.snd ht
    change (R.symm (t, (0 : Fin n → Real))).1 = t at hfst
    change (fun j => sixVertexBetheResidual
      (R.symm (t, (0 : Fin n → Real))).1 N n
      (R.symm (t, (0 : Fin n → Real))).2 j) = 0 at hsnd
    rw [hfst] at hsnd
    exact congrFun (by simpa [roots] using hsnd) j
  have hsource : ∀ᶠ q : Real × (Fin n → Real) in 𝓝 q₀,
      q ∈ R.source := R.open_source.mem_nhds hqsource
  have hunique : ∀ᶠ q : Real × (Fin n → Real) in 𝓝 q₀,
      SixVertexSatisfiesBetheEquations q.1 N n q.2 → roots q.1 = q.2 := by
    filter_upwards [hsource] with q hq hqsol
    have hqzero : (fun j => sixVertexBetheResidual q.1 N n q.2 j) = 0 := by
      funext j
      exact (sixVertexBetheResidual_eq_zero_iff q.1 N n q.2).2 hqsol j
    have hHq : H q = (q.1, (0 : Fin n → Real)) := by
      apply Prod.ext
      · rfl
      · simpa [H, sixVertexBetheResidualGraph] using hqzero
    have hleft := R.left_inv hq
    have hinv : R.symm (q.1, (0 : Fin n → Real)) = q := by
      rw [← hHq]
      simpa [R] using hleft
    exact congrArg Prod.snd hinv
  exact ⟨{
    roots := roots
    analyticAt_roots := hroots
    roots_at := hrootsAt
    eventually_solution := hsolution
    eventually_unique := by simpa [q₀] using hunique
  }⟩


theorem exists_sixVertexLocalAnalyticBetheBranch_of_rootJacobian
    {N n : Nat} {c : Real} (hc : 2 < c) {p : Fin n → Real}
    (hsol : SixVertexSatisfiesBetheEquations c N n p)
    (hjac : Function.Injective (sixVertexBetheRootJacobian N n c p)) :
    Nonempty (SixVertexLocalAnalyticBetheBranch N n c p) :=
  exists_sixVertexLocalAnalyticBetheBranch hc hsol
    (sixVertexBetheResidualGraph_fderiv_injective_of_rootJacobian hc hjac)


theorem isLocalHomeomorphOn_sixVertexBetheContinuationProjection_of_rootJacobian
    {a b : Real} (ha : 2 < a) {N n : Nat} (hN : 0 < N)
    (hhalf : 2 * n ≤ N)
    (C : Set (SixVertexBetheContinuationSpace a b N n))
    (hjac : ∀ q ∈ C,
      Function.Injective (sixVertexBetheRootJacobian N n q.1.1 q.1.2)) :
    IsLocalHomeomorphOn
      (@sixVertexBetheContinuationProjection a b N n) C := by
  rw [isLocalHomeomorphOn_iff_isOpenEmbedding_restrict]
  intro z hzC
  let c : Real := z.1.1
  let p : Fin n → Real := z.1.2
  have hcIcc : c ∈ Set.Icc a b := z.2.1
  have hc : 2 < c := ha.trans_le hcIcc.1
  have hpclosed : SixVertexClosedRootSimplex p := z.2.2.1
  have hpfix : sixVertexBetheUpdate c N n p = p := z.2.2.2
  have hpsol : SixVertexSatisfiesBetheEquations c N n p :=
    (sixVertexBetheUpdate_eq_self_iff hN p).mp hpfix
  have hpopen : SixVertexOpenRootSimplex p :=
    sixVertexBetheUpdate_fixedPoint_mem_open hc hhalf hpclosed hpfix
  obtain ⟨B⟩ := exists_sixVertexLocalAnalyticBetheBranch_of_rootJacobian
    hc hpsol (hjac z hzC)
  obtain ⟨A, hA_sub, hA_open, hqA⟩ :=
    mem_nhds_iff.mp B.eventually_unique
  have hroot_cont : ContinuousAt B.roots c :=
    B.analyticAt_roots.continuousAt
  have hroot_tendsto : Tendsto B.roots (nhds c) (nhds p) := by
    rw [← congrArg nhds B.roots_at]
    exact hroot_cont
  have hgraph_tendsto : Tendsto (fun t => (t, B.roots t))
      (nhds c) (nhds (c, p)) := by
    have heq : (c, B.roots c) = (c, p) := Prod.ext rfl B.roots_at
    rw [← congrArg nhds heq]
    exact continuousAt_id.prodMk hroot_cont
  have hgraphA : ∀ᶠ t in nhds c, (t, B.roots t) ∈ A :=
    hgraph_tendsto.eventually (hA_open.mem_nhds hqA)
  have hrev_tendsto : Tendsto
      (fun t => (t, fun j : Fin n => -B.roots t j.rev))
      (nhds c) (nhds (c, p)) := by
    have hrevroot : ContinuousAt
        (fun t => fun j : Fin n => -B.roots t j.rev) c := by
      rw [continuousAt_pi]
      intro j
      exact ((continuous_apply j.rev).continuousAt.comp hroot_cont).neg
    have hcont := continuousAt_id.prodMk hrevroot
    have hrev_at : (fun j : Fin n => -B.roots c j.rev) = p := by
      rw [B.roots_at]
      exact hpopen.2.1.reverse_neg
    have heq : (c, fun j : Fin n => -B.roots c j.rev) = (c, p) :=
      Prod.ext rfl hrev_at
    rw [← congrArg nhds heq]
    exact hcont
  have hrev_unique : ∀ᶠ t in nhds c,
      SixVertexSatisfiesBetheEquations t N n
          (fun j : Fin n => -B.roots t j.rev) →
        B.roots t = (fun j : Fin n => -B.roots t j.rev) :=
    hrev_tendsto.eventually B.eventually_unique
  have hsymm : ∀ᶠ t in nhds c,
      SixVertexRootSymmetric (B.roots t) := by
    filter_upwards [B.eventually_solution, hrev_unique] with t ht htu
    have heq := htu ht.reverse_neg
    intro j
    have hj := congrFun heq j.rev
    simpa using hj
  let D : Set (Fin n → Real) :=
    {q | StrictMono q ∧ SixVertexRootsInOpenInterval q}
  have hD_open : IsOpen D :=
    isOpen_sixVertexNonsymmetricOpenRootDomain n
  have hpD : p ∈ D := ⟨hpopen.1, hpopen.2.2⟩
  have hrootD : ∀ᶠ t in nhds c, B.roots t ∈ D :=
    hroot_tendsto.eventually (hD_open.mem_nhds hpD)
  let Good : Real → Prop := fun t =>
    ContinuousAt B.roots t ∧
    SixVertexSatisfiesBetheEquations t N n (B.roots t) ∧
    B.roots t ∈ D ∧
    SixVertexRootSymmetric (B.roots t) ∧
    (t, B.roots t) ∈ A
  have hgood : ∀ᶠ t in nhds c, Good t := by
    filter_upwards [B.analyticAt_roots.eventually_continuousAt,
      B.eventually_solution, hrootD, hsymm, hgraphA] with t hct hsol hD hsy hA
    exact ⟨hct, hsol, hD, hsy, hA⟩
  obtain ⟨W, hW_sub, hW_open, hcW⟩ := mem_nhds_iff.mp hgood
  let V : Set (Set.Icc a b) := {t | (t.1 : Real) ∈ W}
  have hV_open : IsOpen V :=
    hW_open.preimage continuous_subtype_val
  let U : Set (SixVertexBetheContinuationSpace a b N n) :=
    {q | q.1 ∈ A ∧ q.1.1 ∈ W}
  have hU_open : IsOpen U :=
    (hA_open.preimage continuous_subtype_val).inter
      (hW_open.preimage continuous_subtype_val.fst)
  have hzU : z ∈ U := ⟨hqA, hcW⟩
  have hbranch_mem (t : V) :
      (t.1.1, B.roots t.1.1) ∈
        sixVertexBetheContinuationSet a b N n := by
    have htgood := hW_sub t.2
    have htopen : SixVertexOpenRootSimplex (B.roots t.1.1) :=
      ⟨htgood.2.2.1.1, htgood.2.2.2.1, htgood.2.2.1.2⟩
    exact ⟨t.1.2, htopen.toClosed,
      (sixVertexBetheUpdate_eq_self_iff hN _).mpr htgood.2.1⟩
  let e : U ≃ V :=
    { toFun := fun q =>
        ⟨sixVertexBetheContinuationProjection q.1, q.2.2⟩
      invFun := fun t =>
        ⟨⟨(t.1.1, B.roots t.1.1), hbranch_mem t⟩,
          (hW_sub t.2).2.2.2.2, t.2⟩
      left_inv := by
        intro q
        apply Subtype.ext
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · have hqsol : SixVertexSatisfiesBetheEquations
              q.1.1.1 N n q.1.1.2 :=
            (sixVertexBetheUpdate_eq_self_iff hN _).mp q.1.2.2.2
          exact hA_sub q.2.1 hqsol
      right_inv := by
        intro t
        apply Subtype.ext
        rfl }
  have he_cont : Continuous e :=
    Continuous.subtype_mk
      (continuous_sixVertexBetheContinuationProjection.comp
        continuous_subtype_val) _
  have he_inv_cont : Continuous e.symm := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    have hrootsV : Continuous (fun t : V => B.roots t.1.1) := by
      rw [continuous_iff_continuousAt]
      intro t
      exact ((hW_sub t.2).1.comp_of_eq
        (continuous_subtype_val.comp continuous_subtype_val).continuousAt rfl)
    exact (continuous_subtype_val.comp continuous_subtype_val).prodMk hrootsV
  let E : U ≃ₜ V := Homeomorph.mk e he_cont he_inv_cont
  refine ⟨U, hU_open.mem_nhds hzU, ?_⟩
  have hemb := hV_open.isOpenEmbedding_subtypeVal.comp E.isOpenEmbedding
  simpa [E, e, U, V, sixVertexBetheContinuationProjection,
    Function.comp_def] using hemb


theorem isLocalHomeomorph_sixVertexBetheContinuationProjection_of_rootJacobian
    {a b : Real} (ha : 2 < a) {N n : Nat} (hN : 0 < N)
    (hhalf : 2 * n ≤ N)
    (hjac : ∀ q ∈ sixVertexBetheContinuationSet a b N n,
      Function.Injective (sixVertexBetheRootJacobian N n q.1 q.2)) :
    IsLocalHomeomorph
      (@sixVertexBetheContinuationProjection a b N n) := by
  rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
  exact isLocalHomeomorphOn_sixVertexBetheContinuationProjection_of_rootJacobian
    ha hN hhalf Set.univ (fun q _ => hjac q.1 q.2)


end
end StatMech.FrontierD

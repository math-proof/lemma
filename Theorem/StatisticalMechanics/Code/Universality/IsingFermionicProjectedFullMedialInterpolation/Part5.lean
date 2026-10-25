/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicProjectedFullMedialInterpolation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialRegularity.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialInterpolation.Part7
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDiscreteInterpolation.Part4
import Def.StatisticalMechanics.Code.Universality.IsingFermionicProjectedFullMedialInterpolation.Part3
open Filter Metric Set Topology


noncomputable section

namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC


namespace FKIsingCaratheodoryApproximation

variable (A : FKIsingCaratheodoryApproximation)


variable {tangent : ∀ n, A.M n → Complex}

variable (I : A.StableFullMedialInterpolation tangent)

theorem StableFullMedialInterpolation.scalingLimit_of_compactBounds_and_moreraPrimitive
    (target Phi : Complex → Complex)
    (htarget : DifferentiableOn Complex target A.U)
    (htarget_ne : target A.root ≠ 0)
    (hPhi : DifferentiableOn Complex Phi A.U)
    (hPhideriv : Set.EqOn (deriv Phi) (fun z => target z ^ 2) A.U)
    (E : StatMech.FrontierA.CompactExhaustion A.U)
    (hbounded : I.HasCompactLocalBounds)
    (hidentify : StableFullMedialInterpolation.SubsequentialMoreraPrimitive
      A I target Phi) :
    TendstoLocallyUniformlyOn I.interpolant target atTop A.U := by
  apply StatMech.FrontierA.tendstoLocallyUniformlyOn_of_subsequential_limits_unique
    I.interpolant target A.U A.isOpen
    (StableFullMedialInterpolation.locallyUniformlySequentiallyPrecompact
      A I E hbounded)
  intro phi psi f hphi hpsi hlimit
  obtain ⟨hMorera, P, C, hP, hPderiv, him, hanchor⟩ :=
    hidentify phi psi f hphi hpsi hlimit
  have hfContinuous : ContinuousOn f A.U :=
    hlimit.continuousOn (Filter.Frequently.of_forall
      (fun n => I.continuousOn (phi (psi n))))
  have hf : DifferentiableOn Complex f A.U :=
    (Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn
      A.isOpen).1 ⟨hMorera, hfContinuous⟩
  have hsquare := isingFermionic_square_eq_of_primitive_im_eq
    f target P Phi A.U A.root C A.isOpen A.isPreconnected A.root_mem
      hP hPhi hPderiv hPhideriv him
  exact isingFermionic_squareRoot_unique_of_anchor
    f target A.U A.root A.isOpen A.isPreconnected A.root_mem hf htarget
      hsquare hanchor htarget_ne


theorem StableFullMedialInterpolation.scalingLimit_of_tensorTentGridHolder
    (H : MeshUniformFullHolder I.interpolant)
    (B : Real) (hanchorBound : ∀ n, ‖I.interpolant n A.root‖ ≤ B)
    (target Phi : Complex → Complex)
    (htarget : DifferentiableOn Complex target A.U)
    (htarget_ne : target A.root ≠ 0)
    (hPhi : DifferentiableOn Complex Phi A.U)
    (hPhideriv : Set.EqOn (deriv Phi) (fun z => target z ^ 2) A.U)
    (E : StatMech.FrontierA.CompactExhaustion A.U)
    (hidentify : StableFullMedialInterpolation.SubsequentialMoreraPrimitive
      A I target Phi) :
    TendstoLocallyUniformlyOn I.interpolant target atTop A.U := by
  exact StableFullMedialInterpolation.scalingLimit_of_compactBounds_and_moreraPrimitive
    A I target Phi htarget htarget_ne hPhi hPhideriv E
      (StableFullMedialInterpolation.hasCompactLocalBounds_of_holder_anchor
        A I H B hanchorBound) hidentify


theorem StableFullMedialInterpolation.projectedLiteralObservable_tendsto_on_compacts
    (hunit : ∀ n e, Complex.normSq (tangent n e) = 1)
    (target : Complex → Complex)
    (hlimit : TendstoLocallyUniformlyOn I.interpolant target atTop A.U)
    (K : Set Complex) (hK : IsCompact K) (hKU : K ⊆ A.U)
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∀ᶠ n in atTop, ∀ e : A.M n, A.medialEmbedding n e ∈ K →
      dist
        (@FKIsingDobrushinDomain.normalizedFermionicObservable
          (A.P n) (A.M n) (A.decEqM n) (A.dobrushin n) (A.mesh n) e)
        (isingProj (tangent n e) (target (A.medialEmbedding n e))) < epsilon := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact A.isOpen] at hlimit
  have hKlimit := hlimit K hKU hK
  rw [Metric.tendstoUniformlyOn_iff] at hKlimit
  filter_upwards [hKlimit epsilon hepsilon] with n hn
  intro e he
  rw [← I.projectedMedial n e]
  exact lt_of_le_of_lt
    (isingProj_dist_le (tangent n e)
      (I.interpolant n (A.medialEmbedding n e))
      (target (A.medialEmbedding n e)) (hunit n e))
    (by simpa only [dist_comm] using hn (A.medialEmbedding n e) he)

end FKIsingCaratheodoryApproximation
end StatMech.Universality
end

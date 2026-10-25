/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDiscreteInterpolation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCaratheodoryApproximation.Part3
import Mathlib.Topology.UniformSpace.Ascoli
import Def.StatisticalMechanics.Code.Universality.IsingFermionicDiscreteInterpolation.Part2
open Filter Metric Set Topology
open scoped UniformConvergence


noncomputable section

namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

namespace FKIsingCaratheodoryApproximation

variable (A : FKIsingCaratheodoryApproximation)


variable (I : A.StableDiscreteInterpolation)


theorem StableDiscreteInterpolation.scalingLimit_of_compactBounds_and_moreraPrimitive
    (target Phi : Complex → Complex)
    (htarget : DifferentiableOn Complex target A.U)
    (htarget_ne : target A.root ≠ 0)
    (hPhi : DifferentiableOn Complex Phi A.U)
    (hPhideriv : Set.EqOn (deriv Phi) (fun z => target z ^ 2) A.U)
    (E : StatMech.FrontierA.CompactExhaustion A.U)
    (hbounded : I.HasCompactLocalBounds)
    (hidentify : StableDiscreteInterpolation.SubsequentialMoreraPrimitive
      A I target Phi) :
    TendstoLocallyUniformlyOn I.interpolant target atTop A.U := by
  apply StatMech.FrontierA.tendstoLocallyUniformlyOn_of_subsequential_limits_unique
    I.interpolant target A.U A.isOpen
    (StableDiscreteInterpolation.locallyUniformlySequentiallyPrecompact
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


theorem StableDiscreteInterpolation.literalObservable_tendsto_on_compacts
    (target : Complex → Complex)
    (hlimit : TendstoLocallyUniformlyOn I.interpolant target atTop A.U)
    (K : Set Complex) (hK : IsCompact K) (hKU : K ⊆ A.U)
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∀ᶠ n in atTop, ∀ e : A.M n, A.medialEmbedding n e ∈ K →
      dist
        (@FKIsingDobrushinDomain.normalizedFermionicObservable
          (A.P n) (A.M n) (A.decEqM n) (A.dobrushin n) (A.mesh n) e)
        (target (A.medialEmbedding n e)) < epsilon := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact A.isOpen] at hlimit
  have hKlimit := hlimit K hKU hK
  rw [Metric.tendstoUniformlyOn_iff] at hKlimit
  filter_upwards [hKlimit epsilon hepsilon] with n hn
  intro e he
  rw [← I.medial n e]
  simpa only [dist_comm] using hn (A.medialEmbedding n e) he

end FKIsingCaratheodoryApproximation
end StatMech.Universality
end

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCaratheodoryHolderAnchor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCaratheodoryApproximation.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicCaratheodoryHolderAnchor.Part2
open Filter Set Topology Metric


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

noncomputable section

namespace FKIsingCaratheodoryApproximation

variable (A : FKIsingCaratheodoryApproximation)


variable (I : A.HolderInterpolation)


theorem eventualMedialBounds_of_holderInterpolation_and_averageEnergy
    (I : A.HolderInterpolation)
    (support : ∀ n, Finset (A.M n))
    (henergy : A.HasEventualCompactAverageEnergy support) :
    ∀ K : Set Complex, IsCompact K → K ⊆ A.U →
      ∃ B : Real, ∀ᶠ n in atTop, ∀ e : A.M n,
        (∃ z ∈ K, dist z (A.medialEmbedding n e) ≤ A.mesh n) →
        ‖@FKIsingDobrushinDomain.normalizedFermionicObservable
          (A.P n) (A.M n) (A.decEqM n) (A.dobrushin n) (A.mesh n) e‖ ≤ B := by
  intro K hK hKU
  obtain ⟨E, hE, henergyEvent⟩ := henergy.1 K hK hKU
  obtain ⟨D, hD, hdiameterEvent⟩ := henergy.2 K hK hKU
  refine ⟨Real.sqrt E + (I.constant : Real) * D ^ (I.exponent : Real), ?_⟩
  filter_upwards [henergyEvent, hdiameterEvent] with n hn hdiameter
  obtain ⟨a, haSupport, haBound⟩ :=
    exists_bounded_anchor_of_average_normSq_le
      (support n) hn.1
      (fun a ↦ @FKIsingDobrushinDomain.normalizedFermionicObservable
        (A.P n) (A.M n) (A.decEqM n) (A.dobrushin n) (A.mesh n) a)
      E hE hn.2
  intro e he
  have hposition := hdiameter a haSupport e he
  have hholder :
      dist
          (@FKIsingDobrushinDomain.normalizedFermionicObservable
            (A.P n) (A.M n) (A.decEqM n) (A.dobrushin n) (A.mesh n) e)
          (@FKIsingDobrushinDomain.normalizedFermionicObservable
            (A.P n) (A.M n) (A.decEqM n) (A.dobrushin n) (A.mesh n) a) ≤
        I.constant * D ^ (I.exponent : Real) := by
    rw [← A.normalizedInterpolant_medial n e,
      ← A.normalizedInterpolant_medial n a]
    exact (I.holder n).dist_le_of_le
      (A.medial_mem_carrier n e) (A.medial_mem_carrier n a) hposition
  calc
    ‖@FKIsingDobrushinDomain.normalizedFermionicObservable
        (A.P n) (A.M n) (A.decEqM n) (A.dobrushin n) (A.mesh n) e‖ ≤
      ‖@FKIsingDobrushinDomain.normalizedFermionicObservable
        (A.P n) (A.M n) (A.decEqM n) (A.dobrushin n) (A.mesh n) a‖ +
      ‖@FKIsingDobrushinDomain.normalizedFermionicObservable
          (A.P n) (A.M n) (A.decEqM n) (A.dobrushin n) (A.mesh n) e -
        @FKIsingDobrushinDomain.normalizedFermionicObservable
          (A.P n) (A.M n) (A.decEqM n) (A.dobrushin n) (A.mesh n) a‖ :=
      norm_le_norm_add_norm_sub' _ _
    _ ≤ Real.sqrt E + (I.constant : Real) * D ^ (I.exponent : Real) := by
      rw [← dist_eq_norm]
      exact add_le_add haBound hholder


theorem scalingLimit_of_holderAverageEnergy_and_primitiveIm
    (I : A.HolderInterpolation) (support : ∀ n, Finset (A.M n))
    (target Phi : Complex → Complex)
    (hhol : ∀ n, DifferentiableOn Complex (A.normalizedInterpolant n) A.U)
    (htarget : DifferentiableOn Complex target A.U)
    (htarget_ne : target A.root ≠ 0)
    (hPhi : DifferentiableOn Complex Phi A.U)
    (hPhideriv : Set.EqOn (deriv Phi) (fun z ↦ target z ^ 2) A.U)
    (E : StatMech.FrontierA.CompactExhaustion A.U)
    (henergy : A.HasEventualCompactAverageEnergy support)
    (hidentifyPrimitive : ∀ (phi psi : Nat → Nat) (f : Complex → Complex),
      StrictMono phi → StrictMono psi →
      TendstoLocallyUniformlyOn
        (fun n ↦ A.normalizedInterpolant (phi (psi n))) f atTop A.U →
      ∃ (P : Complex → Complex) (C : Real),
        DifferentiableOn Complex P A.U ∧
        Set.EqOn (deriv P) (fun z ↦ f z ^ 2) A.U ∧
        (∀ z ∈ A.U, (P z).im = (Phi z).im + C) ∧
        f A.root = target A.root) :
    TendstoLocallyUniformlyOn A.normalizedInterpolant target atTop A.U ∧
      TendstoLocallyUniformlyOn (deriv ∘ A.normalizedInterpolant)
        (deriv target) atTop A.U := by
  apply isingFermionic_scalingLimit_of_compactBounds_and_primitiveIm
    A.mesh A.rawInterpolant target Phi A.U A.root A.isOpen A.isPreconnected
    A.root_mem hhol htarget htarget_ne hPhi hPhideriv E
  · apply compactBounds_of_holderInterpolation_and_eventualMedialBounds
      A I hhol
    exact eventualMedialBounds_of_holderInterpolation_and_averageEnergy
      A I support henergy
  · exact hidentifyPrimitive

end FKIsingCaratheodoryApproximation
end
end StatMech.Universality

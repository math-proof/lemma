/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDenseIncidencePrimitiveBridge.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectedTensorTent.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCenteredRadialPatch.Part12
import Abbrev.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera


namespace StatMech.Universality

open Filter Set Topology

open scoped BigOperators

noncomputable section

namespace FKIsingCaratheodoryApproximation

theorem BoundaryRadialTensorTentGeometry.subsequentialMorera_of_contourError
    (A : FKIsingCaratheodoryApproximation)
    (hU : A.U = Set.univ)
    (G : BoundaryRadialTensorTentGeometry A)
    (H : BoundaryRadialTensorTentGeometry.VanishingRectangleContourError A G) :
    forall (phi psi : Nat -> Nat) (f : Complex -> Complex),
      StrictMono phi -> StrictMono psi ->
      TendstoLocallyUniformlyOn
        (fun n => BoundaryRadialTensorTentGeometry.interpolant A G
          (phi (psi n))) f atTop A.U ->
      Complex.IsConservativeOn f A.U := by
  intro phi psi f hphi hpsi hlimit
  rw [hU] at hlimit ⊢
  exact H.isConservativeOn_subsequentialLimit
    (BoundaryRadialTensorTentGeometry.interpolant_continuous A G)
    (hphi.comp hpsi).tendsto_atTop hlimit


theorem BoundaryRadialTensorTentGeometry.reflected_subsequentialMorera_of_contourError
    (A : FKIsingCaratheodoryApproximation)
    (hU : A.reflect.U = Set.univ)
    (G : BoundaryRadialTensorTentGeometry A)
    (H : BoundaryRadialTensorTentGeometry.ReflectedVanishingRectangleContourError
      A G) :
    forall (phi psi : Nat -> Nat) (f : Complex -> Complex),
      StrictMono phi -> StrictMono psi ->
      TendstoLocallyUniformlyOn
        (fun n => BoundaryRadialTensorTentGeometry.reflectedInterpolant A G
          (phi (psi n))) f atTop A.reflect.U ->
      Complex.IsConservativeOn f A.reflect.U := by
  intro phi psi f hphi hpsi hlimit
  rw [hU] at hlimit ⊢
  exact H.isConservativeOn_subsequentialLimit
    (BoundaryRadialTensorTentGeometry.reflectedInterpolant_continuous A G)
    (hphi.comp hpsi).tendsto_atTop hlimit

end FKIsingCaratheodoryApproximation
end
end StatMech.Universality

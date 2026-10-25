/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialCellularRibbonDuality.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsoradialKacWardLaplacian.Part13


namespace StatMech.FrontierA

open Matrix Finset

open scoped BigOperators

variable {V E D : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype D] [DecidableEq D]


theorem finiteCRSFCycleSupport.toFiber_support {next : V -> V}
    (S : finiteCRSFCycleSupport next) :
    S.toFiber.1.1.support = S.carrier := by
  exact S.ambientPerm_support

theorem finiteCRSFCycleSupport.toCycleSupport_toFiber {next : V -> V}
    (S : finiteCRSFCycleSupport next) :
    S.toFiber.toCycleSupport = S := by
  apply finiteCRSFCycleSupport.ext
  exact S.toFiber_support


theorem finiteCRSFWitnessFiber_support_injective (next : V -> V) :
    Function.Injective
      (fun X : finiteCRSFWitnessFiber next => X.1.1.support) := by
  intro X Y hsupp
  rcases X with ⟨⟨sigma, target⟩, hX⟩
  rcases Y with ⟨⟨tau, target'⟩, hY⟩
  change sigma.support = tau.support at hsupp
  have hperm : sigma = tau := by
    apply Equiv.ext
    intro v
    by_cases hv : sigma v = v
    · have hnot : v ∉ sigma.support := by
        simp [Equiv.Perm.mem_support, hv]
      have hnot' : v ∉ tau.support := by
        rw [← hsupp]
        exact hnot
      have htau : tau v = v := by
        simpa [Equiv.Perm.mem_support] using hnot'
      exact hv.trans htau.symm
    · have hvtau : tau v ≠ v := by
        have hmem : v ∈ sigma.support := Equiv.Perm.mem_support.mpr hv
        rw [hsupp] at hmem
        exact Equiv.Perm.mem_support.mp hmem
      have hsigmaImage : sigma v ∈ sigma.support := by
        rw [Equiv.Perm.mem_support]
        intro h
        exact hv (sigma.injective h)
      have htauImage : tau v ∈ sigma.support := by
        rw [hsupp, Equiv.Perm.mem_support]
        intro h
        exact hvtau (tau.injective h)
      apply (finiteCRSFWitnessNext_injectiveOn_support
        (⟨sigma, target⟩ : finiteCRSFWitness V)) hsigmaImage htauImage
      calc
        finiteCRSFWitnessNext
            (⟨sigma, target⟩ : finiteCRSFWitness V) (sigma v) = v :=
          finiteCRSFWitnessNext_nonfixed_cycle
            (⟨sigma, target⟩ : finiteCRSFWitness V) v hv
        _ = finiteCRSFWitnessNext
            (⟨tau, target'⟩ : finiteCRSFWitness V) (tau v) :=
          (finiteCRSFWitnessNext_nonfixed_cycle
            (⟨tau, target'⟩ : finiteCRSFWitness V) v hvtau).symm
        _ = finiteCRSFWitnessNext
            (⟨sigma, target⟩ : finiteCRSFWitness V) (tau v) := by
          rw [hX, hY]
  subst tau
  have htarget : target = target' := by
    funext v
    calc
      target v = finiteCRSFWitnessNext
          (⟨sigma, target⟩ : finiteCRSFWitness V) v := by
        symm
        simpa using finiteCRSFWitnessNext_fixed
          (⟨sigma, target⟩ : finiteCRSFWitness V) (v : V) v.property
      _ = next v := congrFun hX v
      _ = finiteCRSFWitnessNext
          (⟨sigma, target'⟩ : finiteCRSFWitness V) v :=
        (congrFun hY v).symm
      _ = target' v := by
        simpa using finiteCRSFWitnessNext_fixed
          (⟨sigma, target'⟩ : finiteCRSFWitness V) (v : V) v.property
  subst target'
  rfl

theorem finiteCRSFWitnessFiber.toFiber_toCycleSupport {next : V -> V}
    (X : finiteCRSFWitnessFiber next) :
    X.toCycleSupport.toFiber = X := by
  apply finiteCRSFWitnessFiber_support_injective next
  exact X.toCycleSupport.toFiber_support


end StatMech.FrontierA

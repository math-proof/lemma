/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialCellularRibbonDuality.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardLaplacian.Part11


namespace StatMech.FrontierA

open Matrix Finset

open scoped BigOperators

variable {V E D : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype D] [DecidableEq D]


noncomputable def finiteCRSFWitnessFiber.toCycleSupport
    {next : V -> V} (X : finiteCRSFWitnessFiber next) :
    finiteCRSFCycleSupport next where
  carrier := X.1.1.support
  mapsTo := by
    intro v hv
    have hxv : next v = finiteCRSFWitnessNext X.1 v :=
      (congrFun X.2 v).symm
    rw [hxv]
    have hv' : X.1.1 v ≠ v := Equiv.Perm.mem_support.mp hv
    have hnext : finiteCRSFWitnessNext X.1 v = X.1.1.symm v := by
      simp [finiteCRSFWitnessNext, hv']
    rw [hnext, Equiv.Perm.mem_support]
    intro hfixed
    have hbad : X.1.1 v = v := by
      simpa only [X.1.1.apply_symm_apply] using congrArg X.1.1 hfixed
    exact hv' hbad
  injOn := by
    intro a ha b hb hab
    apply finiteCRSFWitnessNext_injectiveOn_support X.1 ha hb
    calc
      finiteCRSFWitnessNext X.1 a = next a := congrFun X.2 a
      _ = next b := hab
      _ = finiteCRSFWitnessNext X.1 b := (congrFun X.2 b).symm
  noFixed := by
    intro v hv
    have hv' : X.1.1 v ≠ v := Equiv.Perm.mem_support.mp hv
    intro hnext
    have hfixed : finiteCRSFWitnessNext X.1 v = v := by
      rw [X.2]
      exact hnext
    have hfixed' : X.1.1.symm v = v := by
      simpa only [finiteCRSFWitnessNext, dif_neg hv'] using hfixed
    have hbad : v = X.1.1 v := by
      simpa only [X.1.1.apply_symm_apply] using congrArg X.1.1 hfixed'
    exact hv' hbad.symm

end StatMech.FrontierA

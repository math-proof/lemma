module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalEnergy
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialPatch.Part15
public import Mathlib.Data.Nat.Choose.Vandermonde
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRegularity


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRegularity.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

open Finset


noncomputable def fkIsingSquareRadialPatchFullObservableExtension
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) : Nat → Nat → Complex :=
  fun i j ↦
    if hi : i < m then
      if hj : j < m then
        fkIsingSquareRadialPatchFullObservable n m hn hm ⟨i, hi⟩ ⟨j, hj⟩
      else 0
    else 0

end
end StatMech.Universality

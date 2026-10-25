/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/PermCycleQuotientCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialRibbonBoundaryParity.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.PermCycleQuotientCount


namespace StatMech.FrontierA

open Equiv

variable {D : Type*} [Fintype D] [DecidableEq D]


noncomputable def permCycleClassEquivRepresentative (sigma : Perm D) :
    PermCycleClass sigma ≃ PermCycleRepresentative sigma := by
  classical
  let f : PermCycleClass sigma → PermCycleRepresentative sigma :=
    Quot.lift (permCycleRepresentativeOf sigma) fun x y hxy =>
      (permCycleRepresentativeOf_eq_iff_sameCycle sigma x y).2 hxy
  apply Equiv.ofBijective f
  constructor
  · intro a b hab
    induction a using Quot.ind with
    | _ x =>
      induction b using Quot.ind with
      | _ y =>
        apply Quot.sound
        exact (permCycleRepresentativeOf_eq_iff_sameCycle sigma x y).1 hab
  · intro r
    obtain ⟨x, hx⟩ := permCycleRepresentativeOf_surjective sigma r
    exact ⟨Quot.mk _ x, hx⟩


end StatMech.FrontierA

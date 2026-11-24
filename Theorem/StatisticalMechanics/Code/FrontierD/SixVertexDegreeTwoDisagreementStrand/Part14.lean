module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDisagreementComponentCType.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology.Part4
public import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusMedial.Part5
public import Mathlib.Algebra.Group.End
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.GroupTheory.Perm.Cycle.Factors
public import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part15
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

theorem ne_zero_of_intKeepNonzero (z : Int)
    (h : intKeepNonzero z = true) : z ≠ 0 := by
  intro hz
  simp [intKeepNonzero, hz] at h

theorem sum_filter_intKeepNonzero (steps : List Int) :
    (steps.filter intKeepNonzero).sum = steps.sum := by
  induction steps with
  | nil => simp
  | cons step steps ih =>
      by_cases hstep : step = 0 <;>
        simp [intKeepNonzero, hstep, ih]


end
end StatMech.FrontierD

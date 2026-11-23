/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/Integration/ModulusContinuity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.RealAnalysis.code.Integration.Basic.Part2
public import Theorem.Real.Atlas.v1.RealAnalysis.code.Integration.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Finset.Sort
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Bounded

@[expose] public section

open Set Filter Topology Finset


namespace Integration

/-- The modulus of continuity of a function `f` on `[a, b]` at scale `η`:
`w_f(η) = sup {|f(x) - f(y)| : x, y ∈ [a,b], |x - y| ≤ η}`. -/
noncomputable def modulusOfContinuity (f : ℝ → ℝ) (a b η : ℝ) : ℝ :=
  sSup {|f x - f y| | (x ∈ Icc a b) (y ∈ Icc a b) (_ : |x - y| ≤ η)}

end Integration

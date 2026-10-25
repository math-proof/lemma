/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/Integration/ModulusContinuity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.RealAnalysis.code.Integration.Basic.Part2
import Lemma.Real.Atlas.v1.RealAnalysis.code.Integration.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Bounded
open Set Filter Topology Finset


namespace Integration

/-- The modulus of continuity of a function `f` on `[a, b]` at scale `η`:
`w_f(η) = sup {|f(x) - f(y)| : x, y ∈ [a,b], |x - y| ≤ η}`. -/
noncomputable def modulusOfContinuity (f : ℝ → ℝ) (a b η : ℝ) : ℝ :=
  sSup {|f x - f y| | (x ∈ Icc a b) (y ∈ Icc a b) (_ : |x - y| ≤ η)}

end Integration

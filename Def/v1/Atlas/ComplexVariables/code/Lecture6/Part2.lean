/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ComplexVariables/code/Lecture6.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Topology.MetricSpace.Basic
public import Inductive.v1.Atlas.ComplexVariables.code.Lecture6

@[expose] public section

namespace Lecture6

def GeneralizedCircle.toSet : GeneralizedCircle → Set ℂ
  | .circle C => C.toSet
  | .line a b c => {z : ℂ | a * z.re + b * z.im = c}

end Lecture6

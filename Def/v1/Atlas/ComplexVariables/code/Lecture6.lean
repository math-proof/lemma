/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ComplexVariables/code/Lecture6.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Topology.MetricSpace.Basic
import Structure.v1.Atlas.ComplexVariables.code.Lecture6


namespace Lecture6

def Circle.toSet (C : Circle) : Set ℂ :=
  Metric.sphere C.center C.radius

def Circle.Nonintersecting (A B : Circle) : Prop :=
  Disjoint A.toSet B.toSet

def Circle.Concentric (A B : Circle) : Prop :=
  A.center = B.center

end Lecture6

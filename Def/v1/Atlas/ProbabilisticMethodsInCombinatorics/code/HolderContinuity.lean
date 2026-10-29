/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/HolderContinuity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Topology.MetricSpace.HolderNorm


namespace HolderContinuity

open scoped NNReal ENNReal

/-- Definition 9.6.5 (Hölder continuity). A function $f : X \to Y$ between pseudo-emetric
spaces is $\alpha$-Hölder continuous if there exists a constant $C \ge 0$ such that
$d(f(x), f(y)) \le C \cdot d(x, y)^{\alpha}$ for all $x, y \in X$. -/
def IsHolderContinuous {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    (α : NNReal) (f : X → Y) : Prop :=
  ∃ C : NNReal, HolderWith C α f

end HolderContinuity

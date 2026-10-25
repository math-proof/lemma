/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/LipschitzFunctions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open NNReal


namespace LipschitzFunctions

variable {X : Type*} {Y : Type*}

/-- Definition 9.4.7 (Lipschitz functions). A function $f : X \to Y$ is $C$-Lipschitz iff
$d(f(x), f(y)) \le C \cdot d(x, y)$ for all $x, y \in X$. -/
abbrev IsLipschitz [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    (C : ℝ≥0) (f : X → Y) : Prop :=
  LipschitzWith C f

end LipschitzFunctions

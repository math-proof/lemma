/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/OrponenShmerkin2021.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import sympy.atlas.v1.Atlas.ProjectionTheory.code.FurstenbergProposition

namespace FurstenbergSet

open FurstenbergSets


/-- **Orponen–Shmerkin (2021)** sharp lower bound towards the Furstenberg conjecture:
for parameters $0 < s < t$ there exists $\varepsilon > 0$ such that for any constant
$C \ge 1$ there is $c > 0$ so that for every Furstenberg configuration with parameters
$(s, t, C)$, the total tube count satisfies $|\mathbb{T}| \ge c\, \delta^{-(2s + \varepsilon)}$. -/
end FurstenbergSet

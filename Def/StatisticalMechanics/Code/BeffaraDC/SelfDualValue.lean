/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SelfDualValue.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
open Real


namespace StatMech

namespace BeffaraDC

noncomputable def dualParam (p q : ℝ) : ℝ := (1 - p) * q / ((1 - p) * q + p)


noncomputable def selfDualPoint (q : ℝ) : ℝ := Real.sqrt q / (1 + Real.sqrt q)


end BeffaraDC
end StatMech

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/DehnInvariant.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.NumberTheory.Real.Irrational
import Def.v1.Atlas.AlgebraNotes.code.DehnInvariant
open Real TensorProduct Module


namespace DehnInvariant

abbrev DehnGroup := ℝ ⊗[ℤ] (AddCircle (2 * π))

end DehnInvariant

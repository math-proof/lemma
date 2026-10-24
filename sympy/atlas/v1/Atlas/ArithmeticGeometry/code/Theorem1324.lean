/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Theorem1324.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.ProjectiveVarieties
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.ProjectiveVarieties

noncomputable section

set_option maxHeartbeats 400000

open MvPolynomial Finsupp
open scoped LinearAlgebra.Projectivization

namespace Thm1324

variable {n : ℕ} (k : Type*) [Field k]

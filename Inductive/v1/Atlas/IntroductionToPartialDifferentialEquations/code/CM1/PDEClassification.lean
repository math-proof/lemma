/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM1/PDEClassification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open Matrix Finset


namespace PDEClassification

/-- Hadamard's classification of second-order linear PDEs into elliptic, hyperbolic, and
parabolic types, determined by the signature of the leading symbol matrix. -/
inductive PDEType where
  | elliptic
  | hyperbolic
  | parabolic
  deriving DecidableEq, Repr

end PDEClassification

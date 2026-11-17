/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM1/LinearPDEs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import Structure.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM1.LinearPDEs.Part3

@[expose] public section

namespace LinearDifferentialOperator

/-- A linear PDE is homogeneous (Definition 4.0.4) iff its source term $f$ is identically
zero; otherwise it is called inhomogeneous. -/
def LinearPDE.IsHomogeneous {n N : ℕ} (P : LinearPDE n N) : Prop := P.f = 0

end LinearDifferentialOperator

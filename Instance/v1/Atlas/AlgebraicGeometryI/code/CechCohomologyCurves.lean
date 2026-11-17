/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechCohomologyCurves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.LinearAlgebra.Prod
public import Def.v1.Atlas.AlgebraicGeometryI.code.CechCohomologyCurves

@[expose] public section

noncomputable section

namespace CechCohomologyCurves

attribute [instance] CechDataTwoOpen.addCommGroupU1 CechDataTwoOpen.moduleU1
  CechDataTwoOpen.addCommGroupU2 CechDataTwoOpen.moduleU2
  CechDataTwoOpen.addCommGroupU12 CechDataTwoOpen.moduleU12

variable {k : Type*} [Field k]

/-- The first Čech cohomology inherits an additive commutative group structure from the quotient. -/
instance cechH1.addCommGroup (D : CechDataTwoOpen k) : AddCommGroup (cechH1 D) :=
  Submodule.Quotient.addCommGroup _

/-- The first Čech cohomology is a `k`-module via the quotient structure. -/
instance cechH1.module (D : CechDataTwoOpen k) : Module k (cechH1 D) :=
  Submodule.Quotient.module _

end CechCohomologyCurves
end

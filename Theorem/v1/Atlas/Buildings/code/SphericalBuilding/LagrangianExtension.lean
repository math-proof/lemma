/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/LagrangianExtension.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.BilinearForm.Basic

public section

namespace Oriflamme

section ExtendAutomorphism

variable {k : Type*} [Field k]
  {U U' V : Type*} [AddCommGroup U] [AddCommGroup U'] [AddCommGroup V]
  [Module k U] [Module k U'] [Module k V]

end ExtendAutomorphism
end Oriflamme

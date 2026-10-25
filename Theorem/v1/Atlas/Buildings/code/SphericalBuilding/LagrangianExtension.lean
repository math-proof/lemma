/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/LagrangianExtension.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.BilinearForm.Basic


namespace Oriflamme

section ExtendAutomorphism

variable {k : Type*} [Field k]
  {U U' V : Type*} [AddCommGroup U] [AddCommGroup U'] [AddCommGroup V]
  [Module k U] [Module k U'] [Module k V]

end ExtendAutomorphism
end Oriflamme

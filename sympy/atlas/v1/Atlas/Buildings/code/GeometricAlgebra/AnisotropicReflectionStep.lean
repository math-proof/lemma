/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/AnisotropicReflectionStep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.GeometricAlgebra.WittTheorem
import Lemma.Fin.Eq.of.Ne_0.All_Eq

set_option maxHeartbeats 4000000

namespace Garrett

variable {k : Type*} [Field k] [NeZero (2 : k)]
variable {V : Type*} [AddCommGroup V] [Module k V]
variable (B : LinearMap.BilinForm k V)

end Garrett

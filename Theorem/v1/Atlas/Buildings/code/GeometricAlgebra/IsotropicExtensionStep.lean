/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/IsotropicExtensionStep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.GeometricAlgebra.ExtendingIsometries
import Lemma.Submodule.OfEq.eq.M.of.Eq
import Lemma.Fin.Eq.of.Ne_0.All_Eq
import Def.v1.Atlas.Buildings.code.GeometricAlgebra.WittTheorem.Part2
set_option maxHeartbeats 800000


namespace Garrett

variable {k : Type*} [Field k] [NeZero (2 : k)]
variable {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

end Garrett

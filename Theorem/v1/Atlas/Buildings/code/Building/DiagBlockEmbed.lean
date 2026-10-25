/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/DiagBlockEmbed.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Building.IwahoriGLnHelpers
import Lemma.Fin.ValElimMatrix.eq.Transvection.of.Ne
import Def.v1.Atlas.Buildings.code.Building.DiagBlockEmbed
set_option maxHeartbeats 400000

open Matrix


namespace DVRContext

variable (C : DVRContext)

attribute [instance] DVRContext.inst_field DVRContext.inst_comm_ring DVRContext.inst_domain

variable [DVRClosureGL2 C]

section DiagBlockEmbed

variable {n : ℕ}

/-- Every entry of the $1 \times 1$ scalar matrix equals $a$. -/
@[simp] lemma scalarMat1_apply (a : C.k) (i j : Fin 1) : scalarMat1 C a i j = a := by
  simp [scalarMat1, Matrix.of_apply]

end DiagBlockEmbed
end DVRContext

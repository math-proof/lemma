/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/DiagBlockEmbed.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Building.IwahoriGLnHelpers
import Lemma.Fin.ValElimMatrix.eq.Transvection.of.Ne
set_option maxHeartbeats 400000

open Matrix


namespace DVRContext

variable (C : DVRContext)

attribute [instance] DVRContext.inst_field DVRContext.inst_comm_ring DVRContext.inst_domain

variable [DVRClosureGL2 C]

section DiagBlockEmbed

variable {n : ℕ}

/-- The $1 \times 1$ matrix whose single entry is the scalar $a \in k$. -/
noncomputable def scalarMat1 (a : C.k) : Matrix (Fin 1) (Fin 1) C.k :=
  Matrix.of fun _ _ => a

end DiagBlockEmbed
end DVRContext

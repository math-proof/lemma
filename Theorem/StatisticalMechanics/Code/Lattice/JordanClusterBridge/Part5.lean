/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanClusterBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanBridgeCycle.Part10
import Theorem.StatisticalMechanics.Code.Lattice.NoDiagTouchClose.Part4
import Def.StatisticalMechanics.Code.Lattice.JordanClusterBridge.Part5
open SimpleGraph Set


namespace StatMech

namespace Lattice

@[simp] theorem jcb_Lcyc_adj (i j : Fin 8) : jcb_Lcyc.Adj i j ↔ jcb_LcycRel i j := Iff.rfl

end Lattice
end StatMech

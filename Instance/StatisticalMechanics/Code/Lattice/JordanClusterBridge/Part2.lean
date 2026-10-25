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
import Def.StatisticalMechanics.Code.Lattice.JordanClusterBridge.Part3
open SimpleGraph Set


namespace StatMech

namespace Lattice

instance jcb_cyc4_decAdj : DecidableRel jbc_cyc4.Adj := fun i j => by
  rw [jbc_cyc4_adj]; infer_instance


end Lattice
end StatMech

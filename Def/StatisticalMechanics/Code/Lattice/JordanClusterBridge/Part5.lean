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
import Theorem.StatisticalMechanics.Code.Lattice.JordanClusterBridge.Part4
open SimpleGraph Set


namespace StatMech

namespace Lattice

def jcb_LcycRel (i j : Fin 8) : Bool := (i + 1 == j) || (j + 1 == i)


def jcb_Lcyc : SimpleGraph (Fin 8) where
  Adj i j := jcb_LcycRel i j
  symm := by constructor; intro i j h; revert h; revert i j; decide
  loopless := ⟨by intro i h; revert h; revert i; decide⟩

end Lattice
end StatMech

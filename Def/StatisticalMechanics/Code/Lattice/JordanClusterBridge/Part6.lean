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
import Theorem.StatisticalMechanics.Code.Lattice.JordanClusterBridge.Part6
open SimpleGraph Set


namespace StatMech

namespace Lattice

noncomputable def jcb_LPce : PlanarZ2Subgraph where
  V := Fin 8
  finV := inferInstance
  decV := inferInstance
  G := jcb_Lcyc
  emb := ⟨jcb_Lemb, jcb_Lemb_inj⟩
  isSub := jcb_Lemb_isSub


end Lattice
end StatMech

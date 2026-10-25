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
open SimpleGraph Set


namespace StatMech

namespace Lattice

abbrev jcb_BoundedRegion (P : PlanarZ2Subgraph) : Type :=
  {c : (whb_faceRegion (imageGraph P)).ConnectedComponent // c.supp.Finite}


end Lattice
end StatMech

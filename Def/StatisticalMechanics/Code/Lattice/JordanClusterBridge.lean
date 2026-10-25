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
import Abbrev.StatisticalMechanics.Code.Lattice.JordanClusterBridge
open SimpleGraph Set


namespace StatMech

namespace Lattice

noncomputable def jcb_boundedRegionEquiv (P : PlanarZ2Subgraph) :
    jcb_BoundedRegion P ≃ Fin (nullity P.G) :=
  (jed_faithfulDiscreteJordan P).some


end Lattice
end StatMech

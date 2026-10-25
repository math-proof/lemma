/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexTorusDuality.Part10
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusConnected
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.EulerComponentCount.Part2
import Theorem.StatisticalMechanics.Code.FK.TriHexTorusDefectClassify.Part4
open Finset Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

open StatMech.Lattice

open StatMech.Onsager

noncomputable local instance triHexTorusCutDualGraph_decidableRel
    (L : ℕ) [Fact (2 < L)] (S : Set (TorusSite L)) :
    DecidableRel (triHexTorusCutDualGraph L S).Adj := Classical.decRel _


end PeriodicPlanar
end FK
end StatMech

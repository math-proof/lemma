/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Instance.StatisticalMechanics.Code.Exact3D.PolymerEnumeration


namespace StatMech

namespace Exact3D

open StatMech.Lattice

noncomputable section

namespace PolymerSupport

def translationCandidateSet {d : ℕ} (P Q : PolymerSupport d) :
    Finset (Site d) :=
  Q.carrier.biUnion fun y => P.carrier.image fun x => y - x

end PolymerSupport
end
end Exact3D
end StatMech

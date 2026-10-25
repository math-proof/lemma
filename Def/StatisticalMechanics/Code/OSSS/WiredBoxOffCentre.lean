/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxOffCentre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.CenteredFirstHit
import Theorem.StatisticalMechanics.Code.OSSS.WiredBoxLocalized.Part3
import Theorem.StatisticalMechanics.Code.FK.OffCentreDomination.Part13
import Theorem.StatisticalMechanics.Code.FK.CylinderDecayClose.Part6
import Theorem.StatisticalMechanics.Code.OSSS.WiredBoxOffCentre
open scoped BigOperators Classical


namespace StatMech

namespace OSSS

namespace WiredBoxOffCentre

open Lattice IsingFK RevealmentConstruction TreeComplete RevealmentTranslation CenteredFirstHit

open FK

open WiredBoxLocalized

noncomputable def zeroWithinToBoxHom (d m R : Nat) (hmR : m <= R)
    (omega : ConfigSpace (Sym2 (Site d))) :
    openSubgraphInduce d omega (centeredClosedBox (0 : Site d) m) →g
      openSub (boxGraph d R) (boxRestrict d R omega) where
  toFun := fun y => ⟨(y : Site d), by
    apply box_mono d hmR
    rw [mem_box_iff_siteRadius_le, ← centeredRadius_zero]
    exact y.2⟩
  map_rel' := by
    intro y z hyz
    apply boxGraph_open_of_openSubgraph R omega
    exact hyz

end WiredBoxOffCentre
end OSSS
end StatMech

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
import Def.StatisticalMechanics.Code.OSSS.WiredBoxOffCentre
open scoped BigOperators Classical


namespace StatMech

namespace OSSS

namespace WiredBoxOffCentre

open Lattice IsingFK RevealmentConstruction TreeComplete RevealmentTranslation CenteredFirstHit

open FK

open WiredBoxLocalized

@[simp] theorem zeroWithinToBoxHom_val (d m R : Nat) (hmR : m <= R)
    (omega : ConfigSpace (Sym2 (Site d)))
    (y : centeredClosedBox (0 : Site d) m) :
    ((zeroWithinToBoxHom d m R hmR omega y : boxVerts d R) : Site d) = y := rfl

@[simp] theorem zeroWithinToBoxHom_origin (d m R : Nat) (hmR : m <= R)
    (omega : ConfigSpace (Sym2 (Site d))) :
    zeroWithinToBoxHom d m R hmR omega
        ⟨(0 : Site d), center_mem_centeredClosedBox 0 m⟩ =
      IsingFK.boxOrigin d R := by
  apply Subtype.ext
  rfl


end WiredBoxOffCentre
end OSSS
end StatMech

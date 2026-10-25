/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/CenteredFirstHit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.RevealmentTranslation


namespace StatMech

namespace OSSS

namespace CenteredFirstHit

open Lattice RevealmentConstruction RevealmentTranslation


def centeredClosedBox {d : Nat} (u : Site d) (m : Nat) : Set (Site d) :=
  {x | centeredRadius u x <= m}

end CenteredFirstHit
end OSSS
end StatMech

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
import Theorem.StatisticalMechanics.Code.OSSS.WiredBoxOffCentre.Part2
open scoped BigOperators Classical


namespace StatMech

namespace OSSS

namespace WiredBoxOffCentre

open Lattice IsingFK RevealmentConstruction TreeComplete RevealmentTranslation CenteredFirstHit

open FK

open WiredBoxLocalized

def transBoxCenter (d R : Nat) (x : Site d) : fvs_transBoxVerts d R x :=
  ⟨x, by
    show (x - x) ∈ box d R
    simp⟩


def transShellEvent (d k : Nat) (x : Site d) :
    Set (ConfigSpace (Sym2 (fvs_transBoxVerts d (2 * k) x))) :=
  {rho | ∃ y : fvs_transBoxVerts d (2 * k) x,
    centeredRadius x (y : Site d) = k ∧
    (openSub (fvs_transBoxGraph d (2 * k) x) rho).Reachable
      (transBoxCenter d (2 * k) x) y}


def centeredShellEvent (d k : Nat) :
    Set (ConfigSpace (Sym2 (boxVerts d (2 * k)))) :=
  {rho | ∃ y : boxVerts d (2 * k),
    siteRadius (y : Site d) = k ∧
    (openSub (boxGraph d (2 * k)) rho).Reachable
      (IsingFK.boxOrigin d (2 * k)) y}

end WiredBoxOffCentre
end OSSS
end StatMech

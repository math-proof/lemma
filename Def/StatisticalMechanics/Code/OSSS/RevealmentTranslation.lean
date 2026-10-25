/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentTranslation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.RevealmentConstruction.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PathVisitsRow.Part2
import Theorem.StatisticalMechanics.Code.OSSS.RevealmentSum
import Theorem.StatisticalMechanics.Code.OSSS.ReachBoxCrossing.Part2
open Set Finset SimpleGraph


namespace StatMech

namespace OSSS

namespace RevealmentTranslation

open Lattice

open RevealmentConstruction


def siteRadius {d : ℕ} (x : Site d) : ℕ :=
  Finset.univ.sup (fun i => (x i).natAbs)


def centeredRadius {d : ℕ} (u x : Site d) : ℕ :=
  siteRadius (fun i => x i - u i)


def centeredBoundary {d : ℕ} (u : Site d) (n : ℕ) : Set (Site d) :=
  {x | centeredRadius u x = n}

end RevealmentTranslation
end OSSS
end StatMech

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.TrivalentCycles
import Theorem.StatisticalMechanics.Code.Onsager.TurningTelescope.Part3
import Theorem.StatisticalMechanics.Code.Onsager.Torus
import Instance.StatisticalMechanics.Code.Onsager.TorusDecoration.Part2


namespace StatMech.Onsager

open Finset SimpleGraph

open StatMech.Ising

def ons_decInternalNeighbors {L : ℕ} (d : ons_Dart L) : Finset (ons_Dart L) :=
  match d.2 with
  | 0 => {(d.1, 1)}
  | 1 => {(d.1, 0), (d.1, 2)}
  | 2 => {(d.1, 1), (d.1, 3)}
  | 3 => {(d.1, 2)}

end StatMech.Onsager

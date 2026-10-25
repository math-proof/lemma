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
import Theorem.StatisticalMechanics.Code.Onsager.TorusDecoration.Part7


namespace StatMech.Onsager

open Finset SimpleGraph

open StatMech.Ising

def ons_portEdge (L : ℕ) (d : ons_Dart L) : Sym2 (ZMod L × ZMod L) :=
  s(d.1, ons_dirStep L d.2 d.1)

end StatMech.Onsager

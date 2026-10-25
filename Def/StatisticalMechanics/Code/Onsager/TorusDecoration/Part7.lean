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
import Theorem.StatisticalMechanics.Code.Onsager.TorusDecoration.Part6


namespace StatMech.Onsager

open Finset SimpleGraph

open StatMech.Ising

noncomputable def ons_decoratedEdges {L : ℕ} [NeZero L]
    (P : ons_PortPattern L) : Finset (Sym2 (ons_Dart L)) :=
  (ons_decGraph L).edgeFinset.filter (fun e => ons_decEdgeBit P e = 1)

end StatMech.Onsager

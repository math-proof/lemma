/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationCycleExponent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationLoopClassification.Part5
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Theorem.StatisticalMechanics.Code.Onsager.DecorationCycleExponent


namespace StatMech.Onsager

open Finset SimpleGraph

def ons_decExternalStepWalk (L : ℕ) (d : ons_Dart L) :
    (ons_decGraph L).Walk d (ons_dartRev L d) :=
  .cons (Or.inl rfl) .nil

end StatMech.Onsager

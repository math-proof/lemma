module
public import Theorem.StatisticalMechanics.Code.Onsager.DecorationLoopClassification.Part5
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Theorem.StatisticalMechanics.Code.Onsager.DecorationCycleExponent


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationCycleExponent.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Onsager

open Finset SimpleGraph

def ons_decExternalStepWalk (L : ℕ) (d : ons_Dart L) :
    (ons_decGraph L).Walk d (ons_dartRev L d) :=
  .cons (Or.inl rfl) .nil

end StatMech.Onsager

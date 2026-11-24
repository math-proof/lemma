module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.ContourCountInjection.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.PeierlsSingleCircuit.Part2
open Finset Set SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsSingleCircuit.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

attribute [local instance] Classical.propDecidable


def FaceBoundaryConnected (K : Set (Site 2)) (T : Finset (Site 2)) : Prop :=
  ((faceBoundaryGraph K).induce (T : Set (Site 2))).Connected


end Lattice
end StatMech

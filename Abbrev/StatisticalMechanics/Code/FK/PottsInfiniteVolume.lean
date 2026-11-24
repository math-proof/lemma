module
public import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
public import Theorem.StatisticalMechanics.Code.IsingFK.EsWired.Part11
public import Theorem.StatisticalMechanics.Code.IsingFK.EsLatticeBridge
public import Theorem.StatisticalMechanics.Code.IsingFK.FvES.Part4
public import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
public import Theorem.StatisticalMechanics.Code.Foundations.Prokhorov
public import Theorem.StatisticalMechanics.Code.FK.PottsInfiniteVolume.Part5
open MeasureTheory Filter Topology TopologicalSpace
open scoped BigOperators ENNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolume.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace FK

open Lattice


variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


abbrev PottsConfig (d q : ℕ) := Site d → Fin q


abbrev PottsJointConfig (d q : ℕ) :=
  PottsConfig d q × ConfigSpace (Sym2 (Site d))


end FK
end StatMech

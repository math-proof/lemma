module
public import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
public import Theorem.StatisticalMechanics.Code.IsingFK.EsWired.Part11
public import Theorem.StatisticalMechanics.Code.IsingFK.EsLatticeBridge
public import Theorem.StatisticalMechanics.Code.IsingFK.FvES.Part4
public import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
public import Theorem.StatisticalMechanics.Code.Foundations.Prokhorov
public import Theorem.StatisticalMechanics.Code.FK.PottsInfiniteVolume.Part3
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


namespace Wired

open IsingFK

variable (bdry : V → Prop) [DecidablePred bdry]


noncomputable def ivp_wiredJointProb {q : ℕ} (b : Fin q) (beta J : ℝ)
    (z : (V → Fin q) × ConfigSpace (Sym2 V)) : ℝ :=
  esWeightWired G bdry b (1 - Real.exp (-(beta * J))) z.1 z.2 /
    esZWired G bdry q b (1 - Real.exp (-(beta * J)))

end Wired
end FK
end StatMech

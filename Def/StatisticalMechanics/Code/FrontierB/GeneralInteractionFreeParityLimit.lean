/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeParityLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.GeneralInteractionFreeSpinLimit.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.InhomogeneousParityAvoidance.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.PlusBoxCurrentParity.Part3
open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal symmDiff


namespace StatMech.FrontierB

open Sharpness Ising Lattice

def sym2MapEmbedding {V W : Type*} (f : V ↪ W) : Sym2 V ↪ Sym2 W where
  toFun := Sym2.map f
  inj' := Sym2.map.injective f.injective

noncomputable def sym2FinsetMap {V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : V ↪ W) (E : Finset (Sym2 V)) : Finset (Sym2 W) :=
  E.map (sym2MapEmbedding f)

end StatMech.FrontierB

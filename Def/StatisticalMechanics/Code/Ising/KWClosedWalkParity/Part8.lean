/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierEvenToCut.Part8
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourFinal.Part4
import Theorem.StatisticalMechanics.Code.Ising.KWClosedWalkParity.Part10
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Ising

section RegionSide

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Gp Gd : SimpleGraph V} [DecidableRel Gp.Adj] [DecidableRel Gd.Adj]


def DualWalkBoundsRegion (Gp Gd : SimpleGraph V) [DecidableRel Gp.Adj]
    (ψ : Sym2 V ≃ Sym2 V) : Prop :=
  ∀ {w : V} (W : Gd.Walk w w), ∃ S : V → Bool,
    ∀ {u v : V}, Gp.Adj u v →
      (s(u, v) ∈ (W.edges.toFinset).image ψ.symm ↔ S u ≠ S v)

end RegionSide
end Ising
end StatMech

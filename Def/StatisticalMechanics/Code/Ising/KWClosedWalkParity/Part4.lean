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
import Theorem.StatisticalMechanics.Code.Ising.KWClosedWalkParity.Part5
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Ising

section EvenSubgraphDecomp

variable {V : Type*} [Fintype V] [DecidableEq V]

attribute [local instance] Classical.propDecidable

def compF (F : Finset (Sym2 V)) (f : V) : SimpleGraph V where
  Adj a b := (subgraphF F).Adj a b ∧ (subgraphF F).Reachable f a ∧ (subgraphF F).Reachable f b
  symm := by constructor; rintro a b ⟨h, ha, hb⟩; exact ⟨h.symm, hb, ha⟩
  loopless := by refine ⟨fun a ⟨h, _, _⟩ => (subgraphF F).irrefl h⟩

end EvenSubgraphDecomp
end Ising
end StatMech

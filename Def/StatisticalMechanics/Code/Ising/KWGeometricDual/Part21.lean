/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Combinatorics.Graph.Basic
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierClose.Part2
import Theorem.StatisticalMechanics.Code.Walls.fwrfaceregion.Part3
import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part20
open scoped BigOperators
open Finset SimpleGraph Set


namespace StatMech

namespace Ising

open StatMech.Lattice

open StatMech.Walls


noncomputable def kwg_faceSupportGraph {V E : Type*} (ends : E → Sym2 V) :
    SimpleGraph V where
  Adj x y := x ≠ y ∧ ∃ e : E, ends e = s(x, y)
  symm := by
    constructor
    rintro x y ⟨hxy, e, he⟩
    exact ⟨hxy.symm, e, he.trans Sym2.eq_swap⟩
  loopless := ⟨fun x h => h.1 rfl⟩


def kwg_deleteVertexGraph {V : Type*} (G : SimpleGraph V) (v : V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ x ≠ v ∧ y ≠ v
  symm := by
    constructor
    rintro x y ⟨hxy, hx, hy⟩
    exact ⟨hxy.symm, hy, hx⟩
  loopless := ⟨fun x h => G.irrefl h.1⟩


end Ising
end StatMech

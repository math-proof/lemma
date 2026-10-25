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
import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part13
open scoped BigOperators
open Finset SimpleGraph Set


namespace StatMech

namespace Ising

open StatMech.Lattice

open StatMech.Walls


noncomputable def kwg_componentPath {V : Type*} (G : SimpleGraph V) (v : V) :
    G.Walk (G.connectedComponentMk v).out v :=
  (ConnectedComponent.exact (G.connectedComponentMk v).out_eq).some


noncomputable def kwg_componentParityColour {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (D : Finset (Sym2 V)) : V → Bool :=
  fun v => walkParity G D (kwg_componentPath G v)

end Ising
end StatMech

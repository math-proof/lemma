/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicMedialComplex.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDuality
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Mathlib.Combinatorics.SimpleGraph.Matching
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part13


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareVertex_coordinate_bounds (n : Nat)
    (u : (fkSquareBoxPlanar n).V) (i : Fin 2) :
    -(n : Int) ≤ u.1 i ∧ u.1 i ≤ (n : Int) := by
  have hi := u.2 i
  have habs : |u.1 i| ≤ (n : Int) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hi
  exact abs_le.mp habs


end
end StatMech.Universality

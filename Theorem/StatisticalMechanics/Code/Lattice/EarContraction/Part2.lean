/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CornerBalance.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarRemoval.Part5
import Theorem.StatisticalMechanics.Code.Lattice.EarExistence.Part4
import Def.StatisticalMechanics.Code.Lattice.EarContraction.Part2
open SimpleGraph Function


namespace StatMech

namespace Lattice

theorem cellConnected_diff_of_iso (K : Set (Site 2)) (c : Site 2) (hc : c ∈ K)
    (h : (((hypercubicLattice 2).induce K).induce {(⟨c, hc⟩ : K)}ᶜ).Connected) :
    CellConnected (K \ {c}) :=
  Connected.map (diffIso K c hc).toHom (diffIso K c hc).toEquiv.surjective h


theorem cellConnected_diff_of_degree_one (K : Set (Site 2)) (c : Site 2) (hc : c ∈ K)
    (hconn : CellConnected K)
    [Fintype ↑(((hypercubicLattice 2).induce K).neighborSet (⟨c, hc⟩ : K))]
    (hdeg : ((hypercubicLattice 2).induce K).degree (⟨c, hc⟩ : K) = 1) :
    CellConnected (K \ {c}) := by
  apply cellConnected_diff_of_iso K c hc
  exact hconn.induce_compl_singleton_of_degree_eq_one hdeg


end Lattice
end StatMech

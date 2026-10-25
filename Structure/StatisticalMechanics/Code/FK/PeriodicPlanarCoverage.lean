/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoverage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarDualPair.Part3
import Theorem.StatisticalMechanics.Code.FK.TriHexCriticalReduction.Part5
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoverage.Part2
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


namespace PeriodicPlanarDualPair

structure PolynomialConnectionShells
    (D : PeriodicPlanarDualPair P Pdual) where
  level : ℕ → ℕ
  pairs : ∀ n, Finset
    (P.BufferedVertex (level n) × P.BufferedVertex (level n))
  degree : ℕ
  multiplicity : ℕ
  card_le : ∀ n, (pairs n).card ≤ multiplicity * (n + 1) ^ degree
  dist_ge : ∀ n xy, xy ∈ pairs n → n ≤ P.graph.dist xy.1.1 xy.2.1
  planar_limsup :
    ((dualConfigEquiv D.edgeDual) ⁻¹'
      {eta | Pdual.HasInfiniteCluster eta})ᶜ ⊆
      limsup (fun n => P.bufferedPairShell (level n) (pairs n)) atTop

end PeriodicPlanarDualPair
end StatMech.FK.PeriodicPlanar

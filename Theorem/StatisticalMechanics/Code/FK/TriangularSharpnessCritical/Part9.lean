/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriangularSharpnessThreshold
import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredCofinal.Part15
import Theorem.StatisticalMechanics.Code.OSSS.BetaCMatch.Part2
import Def.StatisticalMechanics.Code.FK.TriangularSharpnessCritical.Part9
open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS

open RevealmentTranslation


theorem triangularTransBoxToBufferedAt_injective
    (k : Nat) (x : Site 2) (m : Nat)
    (hm : triangularTransBufferLevel k x ≤ m) :
    Function.Injective (triangularTransBoxToBufferedAt k x m hm) :=
  (triangular.bufferedVertexInclLE hm).injective.comp
    (triangularTransBoxToBuffered_injective k x)

theorem triangularTransBoxToBufferedAt_adjMatch
    (k : Nat) (x : Site 2) (m : Nat)
    (hm : triangularTransBufferLevel k x ≤ m) :
    ocd_AdjMatch (triangularTransBoxGraph (2 * k) x)
      (triangular.bufferedGraph m)
      (triangularTransBoxToBufferedAt k x m hm) := by
  intro y z
  rfl

theorem triangularTransBoxToBufferedAt_inducedWiring_le
    (k : Nat) (hk : 1 ≤ k) (x : Site 2) (m : Nat)
    (hm : triangularTransBufferLevel k x < m)
    (psi : ConfigSpace (Sym2 (triangular.BufferedVertex m))) :
    ocd_inducedWiring (triangular.bufferedGraph m)
        (triangularTransBoxToBufferedAt k x m hm.le)
        (triangular.bufferedBoundary m) psi ≤
      boundaryCliqueGraph (triangularTransBoxBoundary (2 * k) x) := by
  let incl := triangularTransBoxToBufferedAt k x m hm.le
  apply StatMech.FK.ocd_comapInducedWiring_le triangularGraph incl
    (fun _ => rfl)
    (triangularTransBoxToBufferedAt_injective k x m hm.le)
    (triangular.bufferedBoundary m)
    (triangularTransBoxBoundary (2 * k) x)
  · intro y hy
    have hyEarlier : y.1 ∈ triangular.orbitBox
        (triangular.bufferedRadius (triangularTransBufferLevel k x)) :=
      (triangularTransBoxToBuffered k x y).2
    exact (triangular.bufferedBoundary_not_mem_of_lt hm _ hy) hyEarlier
  · intro y z hyz hz
    exact triangularTransBox_boundary_of_adj_outside (by omega) y z hyz hz

end StatMech.FK.PeriodicPlanar

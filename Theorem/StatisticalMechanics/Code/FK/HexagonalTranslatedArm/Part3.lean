/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalTranslatedArm.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.HexagonalSharpnessThreshold
import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredCofinal.Part15
import Def.StatisticalMechanics.Code.FK.HexagonalTranslatedArm.Part3
open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS

open RevealmentTranslation

theorem hexagonalTransBoxToBufferedAt_injective
    (k : Nat) (x : Site 2) (m : Nat)
    (hm : hexagonalTransBufferLevel k x ≤ m) :
    Function.Injective (hexagonalTransBoxToBufferedAt k x m hm) :=
  (hexagonal.bufferedVertexInclLE hm).injective.comp
    (hexagonalTransBoxToBuffered_injective k x)

theorem hexagonalTransBoxToBufferedAt_adjMatch
    (k : Nat) (x : Site 2) (m : Nat)
    (hm : hexagonalTransBufferLevel k x ≤ m) :
    ocd_AdjMatch (hexagonalTransBoxGraph (2 * k) x)
      (hexagonal.bufferedGraph m)
      (hexagonalTransBoxToBufferedAt k x m hm) := by
  intro y z
  rfl

theorem hexagonalTransBoxToBufferedAt_inducedWiring_le
    (k : Nat) (hk : 1 ≤ k) (x : Site 2) (m : Nat)
    (hm : hexagonalTransBufferLevel k x < m)
    (psi : ConfigSpace (Sym2 (hexagonal.BufferedVertex m))) :
    ocd_inducedWiring (hexagonal.bufferedGraph m)
        (hexagonalTransBoxToBufferedAt k x m hm.le)
        (hexagonal.bufferedBoundary m) psi ≤
      boundaryCliqueGraph (hexagonalTransBoxBoundary (2 * k) x) := by
  let incl := hexagonalTransBoxToBufferedAt k x m hm.le
  apply StatMech.FK.ocd_comapInducedWiring_le hexagonalGraph incl
    (fun _ => rfl)
    (hexagonalTransBoxToBufferedAt_injective k x m hm.le)
    (hexagonal.bufferedBoundary m)
    (hexagonalTransBoxBoundary (2 * k) x)
  · intro y hy
    have hyEarlier : y.1 ∈ hexagonal.orbitBox
        (hexagonal.bufferedRadius (hexagonalTransBufferLevel k x)) :=
      (hexagonalTransBoxToBuffered k x y).2
    exact (hexagonal.bufferedBoundary_not_mem_of_lt hm _ hy) hyEarlier
  · intro y z hyz hz
    apply hexagonalTransBox_boundary_of_adj_outside (by omega) y z hyz
    intro hzcoord
    exact hz ⟨hzcoord, Set.mem_univ _⟩

end StatMech.FK.PeriodicPlanar

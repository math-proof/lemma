/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldMacroArrayAssembly.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldArrayClosure.Part3
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

theorem PeriodicPlaneEmbedding.orbitBoxCoordinateBound_le_connectorMarginRequirement
    (E : PeriodicPlaneEmbedding P) (radius : Nat) (i : Fin 2) :
    E.orbitBoxCoordinateBound (P.bufferedRadius radius) i ≤
      E.connectorMarginRequirement radius := by
  rw [PeriodicPlaneEmbedding.connectorMarginRequirement]
  apply le_trans _ (Nat.le_ceil _)
  fin_cases i
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem PeriodicPlaneEmbedding.orbitBox_subset_connectorMarginSquare
    (E : PeriodicPlaneEmbedding P) (radius : Nat) :
    (P.orbitBox (P.bufferedRadius radius) : Set V) ⊆
      E.rectVertices (-(E.connectorMarginRequirement radius : Real))
        (E.connectorMarginRequirement radius)
        (-(E.connectorMarginRequirement radius : Real))
        (E.connectorMarginRequirement radius) := by
  intro v hv
  have hv0 := E.abs_vertexCoord_le_orbitBoxCoordinateBound hv (0 : Fin 2)
  have hv1 := E.abs_vertexCoord_le_orbitBoxCoordinateBound hv (1 : Fin 2)
  have h0 := E.orbitBoxCoordinateBound_le_connectorMarginRequirement radius 0
  have h1 := E.orbitBoxCoordinateBound_le_connectorMarginRequirement radius 1
  rw [abs_le] at hv0 hv1
  exact ⟨by linarith [hv0.1, h0], hv0.2.trans h0,
    by linarith [hv1.1, h1], hv1.2.trans h1⟩


theorem PeriodicPlaneEmbedding.NormalBoundaryBandFamily.exists_fullAlternatingMargins_with_connector
    (E : PeriodicPlaneEmbedding P)
    {mu : Measure (ConfigSpace (Sym2 V))} {S : Finset V} {p : Real}
    (family : E.NormalBoundaryBandFamily mu S p) (radius : Nat) :
    ∃ horizontal vertical : Nat → Nat,
      Tendsto horizontal atTop atTop ∧ Tendsto vertical atTop atTop ∧
      (∀ n, E.connectorMarginRequirement radius ≤ vertical n) ∧
      (∀ n, E.connectorMarginRequirement radius ≤ horizontal (n + 1)) ∧
      (∀ n, (family.radiusLeft (horizontal n) : Int) +
        family.baseLeft 1 ≤ family.baseBottom 1 + vertical n) ∧
      (∀ n, (family.radiusRight (horizontal n) : Int) +
        family.baseRight 1 ≤ family.baseBottom 1 + vertical n) ∧
      (∀ n, (family.radiusLeft (horizontal n) : Int) +
        family.baseTop 1 ≤ family.baseLeft 1 + vertical n) ∧
      (∀ n, (family.radiusRight (horizontal n) : Int) +
        family.baseTop 1 ≤ family.baseRight 1 + vertical n) ∧
      (∀ n, (family.radiusBottom (vertical n) : Int) +
        family.baseBottom 0 ≤ family.baseLeft 0 + horizontal (n + 1)) ∧
      (∀ n, (family.radiusTop (vertical n) : Int) +
        family.baseTop 0 ≤ family.baseLeft 0 + horizontal (n + 1)) ∧
      (∀ n, (family.radiusBottom (vertical n) : Int) +
        family.baseRight 0 ≤ family.baseBottom 0 + horizontal (n + 1)) ∧
      (∀ n, (family.radiusTop (vertical n) : Int) +
        family.baseRight 0 ≤ family.baseTop 0 + horizontal (n + 1)) := by
  simpa only using family.exists_fullAlternatingMargins_with_requirements E
    (fun _ ↦ E.connectorMarginRequirement radius)
    (fun _ ↦ E.connectorMarginRequirement radius)


end StatMech.FK.PeriodicPlanar

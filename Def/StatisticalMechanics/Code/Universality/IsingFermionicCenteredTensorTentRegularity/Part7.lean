/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialCellRegularity
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCenteredRadialPatch.Part12
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera.Part17
import Mathlib.Topology.UnitInterval
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCenteredTensorTentRegularity.Part7


namespace StatMech.Universality

open Metric Set

open scoped unitInterval

noncomputable section

def FKIsingExpandingCenteredNeighborTransport : Prop :=
  ∃ L : NNReal, ∃ N : Nat, ∀ k, N <= k ->
    (∀ a b : Nat,
      ∀ (ha : a + 1 < 2 * fkIsingExpandingSquareSide k)
        (hb : b < 2 * fkIsingExpandingSquareSide k),
      norm
        (fkIsingSquareBoundaryCenteredRadialPatchFullObservable
              (fkIsingExpandingSquareSide k)
              (fkIsingExpandingSquareSide_pos k) ⟨a + 1, ha⟩ ⟨b, hb⟩ /
            (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex) -
          fkIsingSquareBoundaryCenteredRadialPatchFullObservable
              (fkIsingExpandingSquareSide k)
              (fkIsingExpandingSquareSide_pos k) ⟨a, by omega⟩ ⟨b, by omega⟩ /
            (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)) <=
        fkIsingExpandingSquareScale k * (L : Real)) ∧
    (∀ a b : Nat,
      ∀ (ha : a < 2 * fkIsingExpandingSquareSide k)
        (hb : b + 1 < 2 * fkIsingExpandingSquareSide k),
      norm
        (fkIsingSquareBoundaryCenteredRadialPatchFullObservable
              (fkIsingExpandingSquareSide k)
              (fkIsingExpandingSquareSide_pos k) ⟨a, ha⟩ ⟨b + 1, hb⟩ /
            (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex) -
          fkIsingSquareBoundaryCenteredRadialPatchFullObservable
              (fkIsingExpandingSquareSide k)
              (fkIsingExpandingSquareSide_pos k) ⟨a, by omega⟩ ⟨b, by omega⟩ /
            (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)) <=
        fkIsingExpandingSquareScale k * (L : Real))


def FKIsingExpandingCenteredStrictNeighborTransport : Prop :=
  ∃ L : NNReal, ∃ N : Nat, ∀ k, N <= k ->
    (∀ a b : Nat,
      ∀ (ha : a + 1 < 2 * fkIsingExpandingSquareSide k)
        (hb : b < 2 * fkIsingExpandingSquareSide k),
      a + 2 < 2 * fkIsingExpandingSquareSide k ->
      b + 1 < 2 * fkIsingExpandingSquareSide k ->
      norm
        (fkIsingSquareBoundaryCenteredRadialPatchFullObservable
              (fkIsingExpandingSquareSide k)
              (fkIsingExpandingSquareSide_pos k) ⟨a + 1, ha⟩ ⟨b, hb⟩ /
            (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex) -
          fkIsingSquareBoundaryCenteredRadialPatchFullObservable
              (fkIsingExpandingSquareSide k)
              (fkIsingExpandingSquareSide_pos k) ⟨a, by omega⟩ ⟨b, by omega⟩ /
            (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)) <=
        fkIsingExpandingSquareScale k * (L : Real)) ∧
    (∀ a b : Nat,
      ∀ (ha : a < 2 * fkIsingExpandingSquareSide k)
        (hb : b + 1 < 2 * fkIsingExpandingSquareSide k),
      a + 1 < 2 * fkIsingExpandingSquareSide k ->
      b + 2 < 2 * fkIsingExpandingSquareSide k ->
      norm
        (fkIsingSquareBoundaryCenteredRadialPatchFullObservable
              (fkIsingExpandingSquareSide k)
              (fkIsingExpandingSquareSide_pos k) ⟨a, ha⟩ ⟨b + 1, hb⟩ /
            (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex) -
          fkIsingSquareBoundaryCenteredRadialPatchFullObservable
              (fkIsingExpandingSquareSide k)
              (fkIsingExpandingSquareSide_pos k) ⟨a, by omega⟩ ⟨b, by omega⟩ /
            (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)) <=
        fkIsingExpandingSquareScale k * (L : Real))


def isingCenteredRadialIndexSector (n a b : Nat) : Fin 4 :=
  if a < n then
    if b < n then 0 else 1
  else if b < n then 2 else 3


def FKIsingExpandingCenteredHorizontalNeighborBound
    (L : NNReal) (k a b : Nat) : Prop :=
  ∀ (ha : a + 1 < 2 * fkIsingExpandingSquareSide k)
    (hb : b < 2 * fkIsingExpandingSquareSide k),
    norm
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable
            (fkIsingExpandingSquareSide k)
            (fkIsingExpandingSquareSide_pos k) ⟨a + 1, ha⟩ ⟨b, hb⟩ /
          (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex) -
        fkIsingSquareBoundaryCenteredRadialPatchFullObservable
            (fkIsingExpandingSquareSide k)
            (fkIsingExpandingSquareSide_pos k) ⟨a, by omega⟩ ⟨b, by omega⟩ /
          (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)) ≤
      fkIsingExpandingSquareScale k * (L : Real)


def FKIsingExpandingCenteredVerticalNeighborBound
    (L : NNReal) (k a b : Nat) : Prop :=
  ∀ (ha : a < 2 * fkIsingExpandingSquareSide k)
    (hb : b + 1 < 2 * fkIsingExpandingSquareSide k),
    norm
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable
            (fkIsingExpandingSquareSide k)
            (fkIsingExpandingSquareSide_pos k) ⟨a, ha⟩ ⟨b + 1, hb⟩ /
          (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex) -
        fkIsingSquareBoundaryCenteredRadialPatchFullObservable
            (fkIsingExpandingSquareSide k)
            (fkIsingExpandingSquareSide_pos k) ⟨a, by omega⟩ ⟨b, by omega⟩ /
          (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)) ≤
      fkIsingExpandingSquareScale k * (L : Real)


end
end StatMech.Universality

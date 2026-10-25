/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFibreCube.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CollaredWalkCrossing
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangFaithfulExclusive.Part2
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part11
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def RlcTwoChannelFullPhysicalStaticCutConnectivity {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (_hfaith : RlcBookFaithfulTracePair gamma gamma') : Prop :=
  ∀ A : Set (RlcConnectorVertex n),
    (∀ x : RlcConnectorVertex n,
      rlc_connectorOnRight gamma x → x ∈ A) →
    (∀ y : RlcConnectorVertex n,
      rlc_connectorOnLeft gamma' y → y ∉ A) →
    ∃ x y : RlcConnectorVertex n,
      rlc_connectorOnRight gamma x ∧ rlc_connectorOnLeft gamma' y ∧
        (rlc_twoChannelFullPhysicalCutTargetGraphAt
          gamma gamma' A).Reachable x y


def RlcTwoChannelFullPhysicalStaticCutIntersection {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (_hfaith : RlcBookFaithfulTracePair gamma gamma') : Prop :=
  ∀ A B : Set (RlcConnectorVertex n),
    (∀ x : RlcConnectorVertex n,
      rlc_connectorOnRight gamma x → x ∈ A) →
    (∀ y : RlcConnectorVertex n,
      rlc_connectorOnLeft gamma' y → y ∉ A) →
    (∀ x : RlcConnectorVertex n,
      rlc_connectorOnRight gamma x → x ∈ B) →
    (∀ y : RlcConnectorVertex n,
      rlc_connectorOnLeft gamma' y → y ∉ B) →
    ∃ (target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma')
      (x y u v : RlcConnectorVertex n),
      target.1.1 = s(x, y) ∧
        (rlc_twoChannelFullPhysicalSourceEdge target).1 = s(u, v) ∧
        ((u ∈ A ∧ v ∉ A) ∨ (v ∈ A ∧ u ∉ A)) ∧
        ((x ∈ B ∧ y ∉ B) ∨ (y ∈ B ∧ x ∉ B))


def rlc_twoChannelFullPhysicalEdgeCrossesCut {V : Type*}
    (A : Set V) (e : Sym2 V) : Prop :=
  ∃ u v : V, e = s(u, v) ∧
    ((u ∈ A ∧ v ∉ A) ∨ (v ∈ A ∧ u ∉ A))


def PairedEdgeCutIntersection {V I : Type*}
    (source target : I → Sym2 V) (R L : Set V) : Prop :=
  ∀ A B : Set V,
    R ⊆ A → L ∩ A = ∅ → R ⊆ B → L ∩ B = ∅ →
      ∃ i : I, rlc_twoChannelFullPhysicalEdgeCrossesCut A (source i) ∧
        rlc_twoChannelFullPhysicalEdgeCrossesCut B (target i)


def PairedEdgeMonochromatic {V : Type*} (A : Set V) (e : Sym2 V) : Prop :=
  ∀ u v : V, e = s(u, v) → (u ∈ A ↔ v ∈ A)

end
end StatMech.Universality

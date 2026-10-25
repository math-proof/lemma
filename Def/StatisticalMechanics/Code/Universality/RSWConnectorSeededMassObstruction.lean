/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorSeededMassObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorSeededMassCapstone.Part2
import Theorem.StatisticalMechanics.Code.FK.PcNontrivial.Part2
import Theorem.StatisticalMechanics.Code.BeffaraDC.SymmetricDomainSelfDualityObstruction.Part6
import Abbrev.StatisticalMechanics.Code.Universality.RSWConnectorSeededMassObstruction
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def scaleTwoGapCenter : ScaleTwoConnectorVertex :=
  ⟨![0, -1], by simp [rlc_connectorBox, mem_rect]⟩

def scaleTwoGapNorth : ScaleTwoConnectorVertex :=
  ⟨![0, 0], by simp [rlc_connectorBox, mem_rect]⟩

def scaleTwoGapSouth : ScaleTwoConnectorVertex :=
  ⟨![0, -2], by simp [rlc_connectorBox, mem_rect]⟩

def scaleTwoGapEast : ScaleTwoConnectorVertex :=
  ⟨![1, -1], by simp [rlc_connectorBox, mem_rect]⟩

def scaleTwoGapWest : ScaleTwoConnectorVertex :=
  ⟨![-1, -1], by simp [rlc_connectorBox, mem_rect]⟩

def scaleTwoGapNorthEdge : Sym2 ScaleTwoConnectorVertex :=
  s(scaleTwoGapCenter, scaleTwoGapNorth)

def scaleTwoGapSouthEdge : Sym2 ScaleTwoConnectorVertex :=
  s(scaleTwoGapSouth, scaleTwoGapCenter)

def scaleTwoGapEastEdge : Sym2 ScaleTwoConnectorVertex :=
  s(scaleTwoGapEast, scaleTwoGapCenter)

def scaleTwoGapWestEdge : Sym2 ScaleTwoConnectorVertex :=
  s(scaleTwoGapWest, scaleTwoGapCenter)

end
end StatMech.Universality

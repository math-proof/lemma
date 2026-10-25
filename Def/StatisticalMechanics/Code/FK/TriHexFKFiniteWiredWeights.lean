/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredWeights.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredGraphs.Part15
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.FK.ActiveBoundaryEquiv.Part2
open Finset Set
open scoped BigOperators


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice Universality

noncomputable section

def wiredActiveWeight {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (boundary : V → Prop) [DecidablePred boundary]
    (p q : Real) (omega : ConfigSpace G.edgeSet) : Real :=
  wiredFkWeight G boundary p q (extendActive G omega)


def wiredActiveZ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (boundary : V → Prop) [DecidablePred boundary]
    (p q : Real) : Real :=
  ∑ omega : ConfigSpace G.edgeSet,
    wiredActiveWeight G boundary p q omega


def wiredActiveNumer {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (boundary : V → Prop) [DecidablePred boundary]
    (p q : Real) (observable : ConfigSpace G.edgeSet → Real) : Real :=
  ∑ omega : ConfigSpace G.edgeSet,
    observable omega * wiredActiveWeight G boundary p q omega


def wiredActiveRatio {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (boundary : V → Prop) [DecidablePred boundary]
    (p q : Real) (observable : ConfigSpace G.edgeSet → Real) : Real :=
  wiredActiveNumer G boundary p q observable /
    wiredActiveZ G boundary p q


end
end StatMech.FK.PeriodicPlanar

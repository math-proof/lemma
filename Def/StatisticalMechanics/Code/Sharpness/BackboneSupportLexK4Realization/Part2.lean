/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexK4Realization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSupportLexParityBridge.Part7
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSelectorCompatible.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSupportLexK4Realization
open Finset SimpleGraph
open scoped BigOperators

set_option maxHeartbeats 1600000


namespace StatMech.Sharpness

def shbK4Graph (E : Finset shbK4Edge) : SimpleGraph (Fin 4) :=
  SimpleGraph.fromEdgeSet (↑(E.image shbK4Edge.code) : Set (Sym2 (Fin 4)))

end StatMech.Sharpness

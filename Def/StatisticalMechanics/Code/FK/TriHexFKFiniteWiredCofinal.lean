/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredWeights.Part4
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarDiagonalLimit
import Theorem.StatisticalMechanics.Code.FK.BoundaryEdgeAbsorption.Part3
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoverageUpgrade
import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredCofinal
open Finset Set SimpleGraph Filter MeasureTheory Topology


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice Universality

noncomputable section

def triHexPlanarFiniteStarVertexEmbedding (n : Nat) :
    TriHexPlanarFiniteStarVertex n ↪ HexVertex where
  toFun
    | Sum.inl z => (z.1, false)
    | Sum.inr v => (v.1, true)
  inj' := by
    intro u v huv
    rcases u with z | x <;> rcases v with w | y
    · apply congrArg Sum.inl
      exact Subtype.ext (congrArg (fun a : HexVertex => a.1) huv)
    · have := congrArg (fun a : HexVertex => a.2) huv
      simp at this
    · have := congrArg (fun a : HexVertex => a.2) huv
      simp at this
    · apply congrArg Sum.inr
      exact Subtype.ext (congrArg (fun a : HexVertex => a.1) huv)

end
end StatMech.FK.PeriodicPlanar

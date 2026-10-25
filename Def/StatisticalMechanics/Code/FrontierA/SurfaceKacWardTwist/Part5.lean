/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardTwist.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardArf.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardForest
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardTwist.Part4
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

open StatMech.Ising

noncomputable section

noncomputable def surfaceQuadraticEvenPolynomial {g : Nat}
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (edgeClass : Sym2 V → SurfaceHomology g)
    (lambda : SurfaceSpinStructure g) (weight : Sym2 V → Complex) : Complex :=
  ∑ F ∈ G.edgeFinset.powerset.filter IsEvenSubgraph,
    (surfaceParitySign
      (surfaceQuadraticParity lambda (surfaceSubgraphHomology edgeClass F)) : Complex) *
      ∏ edge ∈ F, weight edge

end
end StatMech.FrontierA

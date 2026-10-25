/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPolygonTurning.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardFourSignMajority
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardHalfPlaneSegment
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardInteriorSideSplice
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAntipodalExclusion
import Mathlib.Data.List.Rotate
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardFinitePolygonEar.Part10


namespace StatMech.FrontierA

inductive KWVectorEarDecomposition : List ℂ → Prop
  | triangle (x y z : ℂ)
      (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
      (hsum : x + y + z = 0)
      (hcross : kwComplexCross x y ≠ 0) :
      KWVectorEarDecomposition [x, y, z]
  | contract (previous incoming outgoing next : ℂ) (tail : List ℂ)
      (hp : previous ≠ 0) (hi : incoming ≠ 0)
      (ho : outgoing ≠ 0) (hn : next ≠ 0)
      (hmiddle : kwComplexCross incoming outgoing ≠ 0)
      (hrightTurn :
        (Complex.arg next : Real.Angle) -
          (Complex.arg outgoing : Real.Angle) ≠ (Real.pi : Real.Angle))
      (hleft :
        (0 < kwComplexCross previous incoming ∧
            0 < kwComplexCross previous (incoming + outgoing)) ∨
          (kwComplexCross previous incoming < 0 ∧
            kwComplexCross previous (incoming + outgoing) < 0))
      (hright :
        (0 < kwComplexCross (incoming + outgoing) outgoing ∧
            0 < kwComplexCross (incoming + outgoing) next) ∨
          (kwComplexCross (incoming + outgoing) outgoing < 0 ∧
            kwComplexCross (incoming + outgoing) next < 0))
      (reduced : KWVectorEarDecomposition
        (previous :: (incoming + outgoing) :: next :: tail)) :
      KWVectorEarDecomposition
        (previous :: incoming :: outgoing :: next :: tail)
  | contractPhase (previous incoming outgoing next : ℂ) (tail : List ℂ)
      (hlocal :
        kwVectorTurnPhase previous incoming *
              kwVectorTurnPhase incoming outgoing *
              kwVectorTurnPhase outgoing next =
          kwVectorTurnPhase previous (incoming + outgoing) *
            kwVectorTurnPhase (incoming + outgoing) next)
      (reduced : KWVectorEarDecomposition
        (previous :: (incoming + outgoing) :: next :: tail)) :
      KWVectorEarDecomposition
        (previous :: incoming :: outgoing :: next :: tail)
  | rotate (edges : List ℂ) (r : ℕ)
      (decomposition : KWVectorEarDecomposition edges) :
      KWVectorEarDecomposition (edges.rotate r)


end StatMech.FrontierA

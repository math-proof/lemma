/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalUnequalBridgeGeometry.Part3
import Theorem.StatisticalMechanics.Code.Ising.GHSLebowitz.Part11
import Theorem.StatisticalMechanics.Code.Ising.IsingFKGLayer
import Theorem.StatisticalMechanics.Code.Ising.RectangularPrismTransfer.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part6


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Matrix

open scoped BigOperators

noncomputable section

noncomputable def oddPrismGraphBridgeRawMoment
    (beta : Real) (n : Nat) (r : Real) : Real := by
  letI : DecidableRel (oddPrismLowerBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUpperBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUnequalGlueGraph n).Adj := Classical.decRel _
  exact ∑ a : ConfigSpace (OddPrismLowerBlockSite n),
    ∑ b : ConfigSpace (OddPrismUpperBlockSite n),
      wJ (oddPrismLowerBlockGraph n).edgeFinset (fun _ => beta)
          (fun v => beta * oddPrismPlusField n v.1) a *
        wJ (oddPrismUpperBlockGraph n).edgeFinset (fun _ => beta)
          (fun v => beta * oddPrismPlusField n v.1) b *
        Real.exp (r * unequalReplicaBridgeInteraction
          (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
          (oddPrismUnequalGlueGraph n) a b)

noncomputable def oddPrismGraphBridgeRawFirst
    (beta : Real) (n : Nat) (r : Real) : Real := by
  letI : DecidableRel (oddPrismLowerBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUpperBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUnequalGlueGraph n).Adj := Classical.decRel _
  exact ∑ a : ConfigSpace (OddPrismLowerBlockSite n),
    ∑ b : ConfigSpace (OddPrismUpperBlockSite n),
      wJ (oddPrismLowerBlockGraph n).edgeFinset (fun _ => beta)
          (fun v => beta * oddPrismPlusField n v.1) a *
        wJ (oddPrismUpperBlockGraph n).edgeFinset (fun _ => beta)
          (fun v => beta * oddPrismPlusField n v.1) b *
        (unequalReplicaBridgeInteraction
            (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
            (oddPrismUnequalGlueGraph n) a b *
          Real.exp (r * unequalReplicaBridgeInteraction
            (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
            (oddPrismUnequalGlueGraph n) a b))

noncomputable def oddPrismGraphBridgeRawSecond
    (beta : Real) (n : Nat) (r : Real) : Real := by
  letI : DecidableRel (oddPrismLowerBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUpperBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUnequalGlueGraph n).Adj := Classical.decRel _
  exact ∑ a : ConfigSpace (OddPrismLowerBlockSite n),
    ∑ b : ConfigSpace (OddPrismUpperBlockSite n),
      wJ (oddPrismLowerBlockGraph n).edgeFinset (fun _ => beta)
          (fun v => beta * oddPrismPlusField n v.1) a *
        wJ (oddPrismUpperBlockGraph n).edgeFinset (fun _ => beta)
          (fun v => beta * oddPrismPlusField n v.1) b *
        (unequalReplicaBridgeInteraction
            (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
            (oddPrismUnequalGlueGraph n) a b ^ 2 *
          Real.exp (r * unequalReplicaBridgeInteraction
            (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
            (oddPrismUnequalGlueGraph n) a b))

end
end StatMech.FrontierA

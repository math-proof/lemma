/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxLocalized.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.LocalizedCrossTree
import Theorem.StatisticalMechanics.Code.OSSS.WiredBoxDifferential.Part5
import Theorem.StatisticalMechanics.Code.FK.WiredDomChain.Part4
import Theorem.StatisticalMechanics.Code.FK.OffCentreSandwichProof.Part6
import Theorem.StatisticalMechanics.Code.OSSS.WiredDenominatorArithmetic
import Theorem.StatisticalMechanics.Code.OSSS.WiredBoxLocalized.Part2
open scoped BigOperators Classical


namespace StatMech

namespace OSSS

namespace WiredBoxLocalized

open Lattice RevealmentConstruction AdaptiveCovLowerGeom

open LocalizedCrossTree WiredBoxDifferential

open FK DecisionTree RevealmentTranslation


noncomputable def wiredOuterInnerDenom (d n : Nat) (q beta : Real) : Real :=
  4 * (osssBoxFinset d n).sup' ⟨0, origin_mem_osssBoxFinset d n⟩
    (fun x => ∑ j ∈ Finset.range n,
      Lindeberg.mean
        (FK.activeBCProb (boxGraph d (2 * n))
          (wiredBoxBoundaryGraph d (2 * n))
          (FK.betaParams (fun _ => 1) beta) q)
        (fun omega => if ConnectedToSet d
          (liftCfg (boxActiveEdge d n)
            (restrictConfig (boxActiveEdgeLE d (n_le_two_mul n)) omega))
          x (centeredBoundary x j) then (1 : Real) else 0)) / (n : Real)


noncomputable def wiredOuterInnerConn (d n : Nat) (q beta : Real)
    (x : Site d) (j : Nat) : Real :=
  Lindeberg.mean
    (FK.activeBCProb (boxGraph d (2 * n))
      (wiredBoxBoundaryGraph d (2 * n))
      (FK.betaParams (fun _ => 1) beta) q)
    (fun omega => if ConnectedToSet d
      (liftCfg (boxActiveEdge d n)
        (restrictConfig (boxActiveEdgeLE d (n_le_two_mul n)) omega))
      x (centeredBoundary x j) then (1 : Real) else 0)


noncomputable def wiredOuterInnerTheta (d : Nat) (q beta : Real) (k : Nat) : Real :=
  if k = 0 then 1 else
    Lindeberg.mean
      (FK.activeBCProb (boxGraph d (2 * k))
        (wiredBoxBoundaryGraph d (2 * k))
        (FK.betaParams (fun _ => 1) beta) q)
      (innerCrossInd d k)

noncomputable def wiredOuterInnerSig (d n : Nat) (q beta : Real) : Real :=
  ∑ k ∈ Finset.range n, wiredOuterInnerTheta d q beta k

end WiredBoxLocalized
end OSSS
end StatMech

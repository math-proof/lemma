/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonAbsorptionReduction.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.FiniteEventMultivalued
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
import Theorem.StatisticalMechanics.Code.Percolation.GridBoxConnected.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonStep3FiniteWindow.Part5
open MeasureTheory Set Finset SimpleGraph
open scoped ENNReal NNReal BigOperators


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.Percolation StatMech.ConfigSpace

variable {d : ℕ}


def step3SourceEvent (T : MonotoneAutomaton d) (D N : ℕ)
    (i : (Finset (Site d) × Site d) × Site d) : Set (FieldTriple d) :=
  let M := i.1.1
  let x := i.1.2
  let y := i.2
  {q | step3MaskMatches T D N M q ∧
    (↑(contactForceSet x y) : Set (Site d)) ⊆ ↑M ∧
    l1dist d x y = D ∧
    x ∈ pairLowInfiniteVertices (zeroHighPair T M q) ∧
    y ∈ pairHighCluster (zeroHighPair T M q) 0 ∧
    zeroHighPair T (contactForceSet x y) q ∈
      pairDisjointInfiniteHighAt (0 : Site d) ∧
    pairHighCluster (zeroHighPair T (contactForceSet x y) q) 0 =
      pairHighCluster (zeroHighPair T M q) 0}

def step3TargetEvent (T : MonotoneAutomaton d) (D N : ℕ)
    (i : (Finset (Site d) × Site d) × Site d) : Set (FieldTriple d) :=
  step3SourceEvent T D N i ∩
    highThresholdOn T.threshold (contactForceSet i.1.2 i.2)

end StatMech.FrontierA

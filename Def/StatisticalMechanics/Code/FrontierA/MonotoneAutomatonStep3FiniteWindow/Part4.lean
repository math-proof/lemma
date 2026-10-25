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
import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonStep3FiniteWindow.Part4
open MeasureTheory Set Finset SimpleGraph
open scoped ENNReal NNReal BigOperators


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.Percolation StatMech.ConfigSpace

variable {d : ℕ}


noncomputable def step3Indices (N : ℕ) :
    Finset ((Finset (Site d) × Site d) × Site d) :=
  ((boxFinsetBK d N).powerset.product (boxFinsetBK d N)).product
    (boxFinsetBK d N)

def step3MaskMatches (T : MonotoneAutomaton d) (D N : ℕ)
    (M : Finset (Site d)) (q : FieldTriple d) : Prop :=
  ∀ z : Site d, z ∈ M ↔ z ∈ boxFinsetBK d N ∧
    ∃ a : Site d, a ∈ pairLowInfiniteVertices (zeroHighPair T M q) ∧
      l1dist d a z < D

end StatMech.FrontierA

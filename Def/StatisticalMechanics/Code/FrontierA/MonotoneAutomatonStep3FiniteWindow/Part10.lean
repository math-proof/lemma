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
import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonStep3FiniteWindow.Part10
open MeasureTheory Set Finset SimpleGraph
open scoped ENNReal NNReal BigOperators


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.Percolation StatMech.ConfigSpace

variable {d : ℕ}


noncomputable def step3WindowContacts (T : MonotoneAutomaton d)
    (D N : ℕ) (q : FieldTriple d) : Finset (Site d × Site d) :=
  by
    classical
    exact ((boxFinsetBK d N).product (boxFinsetBK d N)).filter fun p =>
      q ∈ step3ContactEvent T D p

def step3CoreWindowEvent (T : MonotoneAutomaton d) (D N K : ℕ) :
    Set (FieldTriple d) :=
  (interpolatedHighPair T) ⁻¹' pairStep3DistanceAt (0 : Site d) D ∩
    {q | K ≤ (step3WindowContacts T D N q).card}

end StatMech.FrontierA

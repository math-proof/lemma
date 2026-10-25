/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusParityPatternMixing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.PlusEvenMixing.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.PlusParityPatternMixing
open MeasureTheory Set
open scoped BigOperators


namespace StatMech.FrontierB

open Sharpness Ising Lattice

open StatMech.ConfigSpace StatMech.FK

noncomputable def plusParityPatternSpinPolynomial {d : Nat} (beta : Real)
    (S : Finset (Sym2 (Site d))) (odd : ↑S -> Bool)
    (omega : ConfigSpace (Site d)) : Real :=
  ∑ T ∈ S.powerset, currentParityTraceCoeff S odd T *
    Real.cosh beta ^ T.card * Real.exp (-beta * edgeSpinSum T omega)

end StatMech.FrontierB

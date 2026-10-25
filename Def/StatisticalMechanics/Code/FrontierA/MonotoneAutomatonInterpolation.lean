/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonInterpolation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonLaw.Part4
import Abbrev.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonInterpolation
open MeasureTheory


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

variable {d : ℕ}


def tripleFieldShift (g : Multiplicative (Site d)) (q : FieldTriple d) :
    FieldTriple d :=
  (fieldShift g q.1, fieldShift g q.2.1, fieldShift g q.2.2)

end StatMech.FrontierA

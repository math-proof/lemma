/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWTraceContact.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part101
import Theorem.StatisticalMechanics.Code.Universality.RSWTraceContact
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


noncomputable def rlc_ambientCrossingWalk {a b c d : ℤ}
    (gamma : RlcCrossingPath a b c d) :
    (hypercubicLattice 2).Walk
      (gamma.1 : Site 2) (gamma.2.1 : Site 2) :=
  gamma.2.2.1.map
    (SimpleGraph.Embedding.induce (G := hypercubicLattice 2)
      (rect a b c d)).toHom


end Universality
end StatMech

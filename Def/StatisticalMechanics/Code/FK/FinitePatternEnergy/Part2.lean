/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FinitePatternEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.CircuitLowerBound.Part6
import Theorem.StatisticalMechanics.Code.FK.FKDisjointBoxDomainMarkov.Part3
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Theorem.StatisticalMechanics.Code.FK.FinitePatternEnergy.Part2
open MeasureTheory Finset


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


variable (C : SimpleGraph V) [DecidableRel C.Adj]


variable {C}


variable (C : SimpleGraph V) [DecidableRel C.Adj]


variable {C}


def patternEvent (I : Finset (Sym2 V)) (eta : ConfigSpace ↥I) :
    Set (ConfigSpace (Sym2 V)) :=
  {omega | I.restrict omega = eta}

end FK
end StatMech

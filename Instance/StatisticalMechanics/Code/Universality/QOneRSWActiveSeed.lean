/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/QOneRSWActiveSeed.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWConcreteSeed.Part3
import Theorem.StatisticalMechanics.Code.Universality.RSWQOneRectangleCylinder
import Theorem.StatisticalMechanics.Code.Universality.RSWFailureComplementaryArcObstruction.Part8
import Abbrev.StatisticalMechanics.Code.Universality.QOneRSWActiveSeed
open Set SimpleGraph MeasureTheory
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Lattice

open StatMech.Percolation

open StatMech.FK

open StatMech.RSW.Box


noncomputable instance rq1ActiveExtremalPairFintype (n : ℤ) :
    Fintype (Rq1ActiveExtremalPair n) :=
  Fintype.ofFinite _


end Universality
end StatMech

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConcreteSeed.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part101
import Theorem.StatisticalMechanics.Code.Universality.CrossingReflection.Part4
import Theorem.StatisticalMechanics.Code.Universality.RSWConcreteSeed
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Lattice

open StatMech.Percolation

open StatMech.RSW.Box


noncomputable def rcs_rightLower (n : ℤ) :
    Finset (rect 0 (2 * n) (-n) n) :=
  rlc_verticalSegment 0 (2 * n) (-n) n 0 (-n) 0

noncomputable def rcs_rightUpper (n : ℤ) :
    Finset (rect 0 (2 * n) (-n) n) :=
  rlc_verticalSegment 0 (2 * n) (-n) n (2 * n) 0 n

noncomputable def rcs_leftLower (n : ℤ) :
    Finset (rect (-2 * n) 0 (-n) n) :=
  rlc_verticalSegment (-2 * n) 0 (-n) n (-2 * n) (-n) 0

noncomputable def rcs_leftUpper (n : ℤ) :
    Finset (rect (-2 * n) 0 (-n) n) :=
  rlc_verticalSegment (-2 * n) 0 (-n) n 0 0 n

end Universality
end StatMech

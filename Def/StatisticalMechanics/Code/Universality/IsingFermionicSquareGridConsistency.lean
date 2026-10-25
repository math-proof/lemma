/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareGridConsistency.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Analysis.Calculus.Taylor


namespace StatMech.Universality

open Set

noncomputable section

def cubicTaylorPolynomial (g : Real → Real) (s : Real) : Real :=
  g 0 + iteratedDeriv 1 g 0 * s +
    iteratedDeriv 2 g 0 * s ^ 2 / 2 +
      iteratedDeriv 3 g 0 * s ^ 3 / 6

end
end StatMech.Universality

module
public import Theorem.StatisticalMechanics.Code.SLE.BrownianDyadicApproximation.Part2
public import Theorem.StatisticalMechanics.Code.SLE.BrownianContinuousModification
open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianContinuousModification.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.SLE

noncomputable def brownianCompactRadius (t : Real) : Nat := Nat.ceil |t|

end StatMech.SLE

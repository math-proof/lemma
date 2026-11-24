module
public import Theorem.StatisticalMechanics.Code.Inequalities.Pivotal.Part2
public import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterfly
public import Theorem.StatisticalMechanics.Code.Inequalities.ReimerFiberClose.Part2
public import Theorem.StatisticalMechanics.Code.FK.RussoDerivativeBetaSum
public import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterionInhom.Part2
public import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldPercoInhom.Part3
open Finset SimpleGraph Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldPercoInhom.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Sharpness

open ConfigSpace

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


def mpiPivotalClosed (e : Sym2 V) (A : Set (ConfigSpace (Sym2 V))) :
    Set (ConfigSpace (Sym2 V)) :=
  {omega | IsPivotal e A omega ∧ omega e = false}

end Sharpness
end StatMech

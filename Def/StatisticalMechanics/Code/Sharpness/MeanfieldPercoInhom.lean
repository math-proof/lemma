/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldPercoInhom.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.Pivotal.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterfly
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerFiberClose.Part2
import Theorem.StatisticalMechanics.Code.FK.RussoDerivativeBetaSum
import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterionInhom.Part2
open Finset SimpleGraph Set


namespace StatMech

namespace Sharpness

open ConfigSpace

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


def mpiCrossingEvent (o : V) (B : Set V) : Set (ConfigSpace (Sym2 V)) :=
  connEvent G Set.univ o B


noncomputable def mpiBlockedSet (B : Set V) (omega : ConfigSpace (Sym2 V)) : Finset V :=
  by
    classical
    exact Finset.univ.filter fun x => ¬ ConnToSet G omega Set.univ x B


def mpiSurfaceEvent (B : Set V) (S : Finset V) : Set (ConfigSpace (Sym2 V)) :=
  {omega | mpiBlockedSet G B omega = S}

end Sharpness
end StatMech

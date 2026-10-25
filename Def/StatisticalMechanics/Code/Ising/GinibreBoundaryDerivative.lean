/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GinibreBoundaryDerivative.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.GinibreBoundary
open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false


namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]


def inhomogeneousInteraction
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (h : V -> Real)
    (s : ConfigSpace V) : Real :=
  (∑ e ∈ E, J e * bond s e) + ∑ v : V, h v * spin s v


def scaledInhomogeneousPartition
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (h : V -> Real)
    (beta : Real) : Real :=
  ZJ E (fun e => beta * J e) (fun v => beta * h v)


def scaledMeanInteraction
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (h : V -> Real)
    (beta : Real) : Real :=
  expJ E (fun e => beta * J e) (fun v => beta * h v)
    (inhomogeneousInteraction E J h)


def boundaryInterfaceFreeEnergy
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hPlus h : V -> Real) (beta : Real) : Real :=
  Real.log (scaledInhomogeneousPartition E J hPlus beta) -
    Real.log (scaledInhomogeneousPartition E J h beta)

end
end StatMech.Ising

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABMeanfieldGhost.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldTargetReassembly.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.ABFiniteAssembly.Part2
open Finset Set SimpleGraph


namespace StatMech

namespace Sharpness

open ConfigSpace RandomCurrent

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def abmgPhi (J : Sym2 V -> Real) (o : V)
    (beta h : Real) (S : Finset (Option V)) : Real :=
  mtrPhi (withGhost G) (abfaParams G J beta h)
    (FieldGhostDict.origEdges G) (some o) S


noncomputable def abmgTargetMag (J : Sym2 V -> Real) (o : V)
    (B : Set (Option V)) (beta h : Real) : Real :=
  probV (abfaParams G J beta h)
    (connEvent (withGhost G) Set.univ (some o) B)


noncomputable def abmgTargetPhi (J : Sym2 V -> Real) (o : V)
    (B : Set (Option V)) (beta h : Real) (S : Finset (Option V)) : Real :=
  mtrPhi (withGhost G) (abfaParams G J beta h)
    (FieldGhostDict.origEdges G) (some o) S


end Sharpness
end StatMech

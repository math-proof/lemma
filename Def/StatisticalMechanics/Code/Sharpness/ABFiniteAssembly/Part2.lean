/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFiniteAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.ABCouplingReindex.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.ABPhysicalDeriv.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.ABFiniteAssembly
open Finset Set SimpleGraph


namespace StatMech

namespace Sharpness

open ConfigSpace RandomCurrent

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def abfaParams (J : Sym2 V → ℝ) (beta h : ℝ) :
    Sym2 (Option V) → ℝ :=
  abpdBetaFieldParams (FieldGhostDict.ghostEdges V) (qField h)
    (abfaLiftCoupling G J) beta


noncomputable def abfaMag (J : Sym2 V → ℝ) (o : V) (beta h : ℝ) : ℝ :=
  probV (abfaParams G J beta h)
    (connEvent (withGhost G) Set.univ (some o) {none})


end Sharpness
end StatMech

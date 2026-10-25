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
open Finset Set SimpleGraph


namespace StatMech

namespace Sharpness

open ConfigSpace RandomCurrent

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def abfaBaseCoupling (J : Sym2 V → ℝ) (e : Sym2 V) : ℝ :=
  if e ∈ G.edgeFinset then J e else 0


noncomputable def abfaLiftCoupling (J : Sym2 V → ℝ) : Sym2 (Option V) → ℝ :=
  FieldGhostDict.ghostCoupling 0 1 (abfaBaseCoupling G J)

end Sharpness
end StatMech

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedDomain.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedPeriodic.Part3
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Def.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedDomain.Part2
open scoped BigOperators Classical
open Finset Set

set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

variable (C : SimpleGraph V) [DecidableRel C.Adj]


theorem inducedBcZW_pos {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 0 < q) (F : Finset (Sym2 V))
    (psi : ConfigSpace (Sym2 V)) : 0 < inducedBcZW G C pf q F psi := by
  unfold inducedBcZW
  exact Finset.sum_pos (fun rho _ => bcWeightW_pos G C hpf hpf1 hq rho)
    ⟨psi, self_mem_condFibre F psi⟩


end FK
end StatMech

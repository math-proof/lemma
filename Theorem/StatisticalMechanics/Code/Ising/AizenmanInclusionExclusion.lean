/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanInclusionExclusion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.Switching.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.MultiReplica.Part2
import Theorem.StatisticalMechanics.Code.Ising.AizenmanSignDominance.Part2
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Sharpness

namespace RandomCurrent

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]


theorem aie_conn_trans_xy (ends : ι → Sym2 V) (m : Finset ι) {o x y : V}
    (hoy : connK ends m o y) (hox : connK ends m o x) : connK ends m x y :=
  Relation.ReflTransGen.trans (connK_symm ends m hox) hoy


theorem aie_conn_trans_ox (ends : ι → Sym2 V) (m : Finset ι) {o x y : V}
    (hxy : connK ends m x y) (hoy : connK ends m o y) : connK ends m o x :=
  Relation.ReflTransGen.trans hoy (connK_symm ends m hxy)


theorem aie_conn_trans_oy (ends : ι → Sym2 V) (m : Finset ι) {o x y : V}
    (hxy : connK ends m x y) (hox : connK ends m o x) : connK ends m o y :=
  Relation.ReflTransGen.trans hox hxy


end RandomCurrent
end Sharpness
end StatMech

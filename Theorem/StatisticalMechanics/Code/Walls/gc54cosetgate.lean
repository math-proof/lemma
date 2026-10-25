/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc54cosetgate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc53count.Part3
open Finset BigOperators SimpleGraph
open scoped symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.multiGoal false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000


namespace StatMech.Walls

open StatMech.Sharpness.RandomCurrent (sources connK connK_symm sources_symmDiff mem_sources
  path_exists exists_conn_set)

section Abstract

open Classical

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]


theorem gc54_gate_monotone (ends : ι → Sym2 W) (K : Finset ι) {m₁ m₂ : Finset ι} (h : m₁ ⊆ m₂)
    {x g : W} (hgate : connK ends (K ∪ m₁) x g) : connK ends (K ∪ m₂) x g :=
  gc51_connK_mono ends (Finset.union_subset_union_right h) hgate


theorem gc54_gate_disjoint_eq (ends : ι → Sym2 W) (K : Finset ι) {L P₀ : Finset ι}
    (hdisj : Disjoint L P₀) {x g : W} (hgate : connK ends (K ∪ L) x g) :
    connK ends (K ∪ (L ∆ P₀)) x g := by
  have hun : L ∆ P₀ = L ∪ P₀ := Disjoint.symmDiff_eq_sup hdisj
  rw [hun]
  exact gc54_gate_monotone ends K Finset.subset_union_left hgate


theorem gc54_LblockSet_eq (ends : ι → Sym2 W) (K : Finset ι) (o x g : W) :
    gc51_LblockSet ends K o x g
      = (univ \ K).powerset.filter
          (fun L => sources ends L = (∅ : Finset W) ∧ connK ends (K ∪ L) x g) := rfl


theorem gc54_cosetGateBlock_eq (ends : ι → Sym2 W) (K P₀ : Finset ι) (o x g : W) :
    gc53_cosetGateBlock ends K P₀ o x g
      = (univ \ K).powerset.filter
          (fun L => sources ends L = (∅ : Finset W) ∧ connK ends (K ∪ (L ∆ P₀)) x g) := rfl


end Abstract
end StatMech.Walls

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc7connequiv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.Switching.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc6_pairingpath
open Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.Walls

open StatMech.Sharpness

open StatMech.Sharpness.RandomCurrent

open StatMech.Sharpness.FluxEdgeCopy

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]


omit [DecidableEq ι] [Fintype V] [Fintype ι] in


theorem gc7_connK_refl (ends : ι → Sym2 V) (K : Finset ι) (a : V) :
    connK ends K a a :=
  Relation.ReflTransGen.refl

omit [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι] in


theorem gc7_connK_symm (ends : ι → Sym2 V) (K : Finset ι) {a b : V}
    (h : connK ends K a b) : connK ends K b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      rcases hstep with ⟨i, hi, ha, hb, hne⟩
      exact Relation.ReflTransGen.head ⟨i, hi, hb, ha, hne.symm⟩ ih

omit [DecidableEq ι] [Fintype V] [Fintype ι] in


theorem gc7_connK_trans (ends : ι → Sym2 V) (K : Finset ι) {a b c : V}
    (h₁ : connK ends K a b) (h₂ : connK ends K b c) : connK ends K a c :=
  h₁.trans h₂


omit [DecidableEq ι] [Fintype V] [Fintype ι] in


theorem gc7_connK_equivalence (ends : ι → Sym2 V) (K : Finset ι) :
    Equivalence (connK ends K) :=
  ⟨fun a => gc7_connK_refl ends K a,
   fun h => gc7_connK_symm ends K h,
   fun h₁ h₂ => gc7_connK_trans ends K h₁ h₂⟩


end StatMech.Walls

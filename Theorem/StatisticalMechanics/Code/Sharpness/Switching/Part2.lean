/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Switching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Sharpness.Switching.Part2
open Finset BigOperators
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false


namespace StatMech

namespace Sharpness

namespace RandomCurrent

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]


lemma adjStep_symm (ends : ι → Sym2 V) (K : Finset ι) {a b : V} :
    adjStep ends K a b → adjStep ends K b a := by
  rintro ⟨i, hi, ha, hb, hne⟩; exact ⟨i, hi, hb, ha, hne.symm⟩

lemma connK_symm (ends : ι → Sym2 V) (K : Finset ι) {a b : V} :
    connK ends K a b → connK ends K b a := by
  intro h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.head (adjStep_symm ends K hstep) ih


end RandomCurrent
end Sharpness
end StatMech

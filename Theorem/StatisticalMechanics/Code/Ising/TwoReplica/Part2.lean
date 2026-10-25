/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoReplica.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Ising.TwoReplica.Part2
open Finset Classical
open scoped symmDiff BigOperators

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (E : Finset (Sym2 V))


lemma adjP_symm (P : Finset (Sym2 V)) {a b : V} : adjP P a b → adjP P b a := by
  rintro ⟨e, he, ha, hb, hne⟩; exact ⟨e, he, hb, ha, hne.symm⟩

lemma connP_symm (P : Finset (Sym2 V)) {a b : V} : connP P a b → connP P b a := by
  intro h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.head (adjP_symm P hstep) ih

lemma connP_mono {P Q : Finset (Sym2 V)} (hPQ : P ⊆ Q) {a b : V} (h : connP P a b) :
    connP Q a b := by
  refine Relation.ReflTransGen.mono ?_ _ _ h
  rintro x y ⟨e, he, hx, hy, hne⟩; exact ⟨e, hPQ he, hx, hy, hne⟩


end Ising
end StatMech

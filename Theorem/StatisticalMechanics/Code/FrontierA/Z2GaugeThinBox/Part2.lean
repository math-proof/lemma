/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeThinBox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeIsingAdapter
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeThinBox
open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

noncomputable section

theorem thinBoxPlaquetteEdge_injective (n : ℕ) :
    Function.Injective (thinBoxPlaquetteEdge n) := by
  intro i j hij
  have hedge : s(i.castSucc, i.succ) = s(j.castSucc, j.succ) :=
    congrArg Subtype.val hij
  rcases Sym2.eq_iff.mp hedge with h | h
  · exact Fin.ext (by simpa using congrArg Fin.val h.1)
  · have hleft := congrArg Fin.val h.1
    have hright := congrArg Fin.val h.2
    simp only [Fin.val_castSucc, Fin.val_succ] at hleft hright
    omega

theorem thinBoxPlaquetteEdge_surjective (n : ℕ) :
    Function.Surjective (thinBoxPlaquetteEdge n) := by
  rintro ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
      have hadj : u.val + 1 = v.val ∨ v.val + 1 = u.val := by
        simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
          SimpleGraph.pathGraph_adj] using he
      rcases hadj with huv | hvu
      · let i : Fin n := ⟨u.val, by omega⟩
        refine ⟨i, ?_⟩
        apply Subtype.ext
        change s(i.castSucc, i.succ) = s(u, v)
        apply Sym2.eq_iff.mpr
        left
        constructor <;> apply Fin.ext <;> simp [i, huv]
      · let i : Fin n := ⟨v.val, by omega⟩
        refine ⟨i, ?_⟩
        apply Subtype.ext
        change s(i.castSucc, i.succ) = s(u, v)
        apply Sym2.eq_iff.mpr
        right
        constructor <;> apply Fin.ext <;> simp [i, hvu]


end
end StatMech.FrontierA

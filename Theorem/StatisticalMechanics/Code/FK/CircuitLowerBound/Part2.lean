/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CircuitLowerBound.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.FiniteEnergy.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.Pivotal.Part2
import Def.StatisticalMechanics.Code.FK.CircuitLowerBound
open scoped BigOperators


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


omit [Fintype V] in
@[simp] theorem closeAllOn_of_mem {γ : Finset (Sym2 V)} {e : Sym2 V} (he : e ∈ γ)
    (ψ : ConfigSpace (Sym2 V)) : closeAllOn γ ψ e = false := by simp [closeAllOn, he]

omit [Fintype V] in
theorem closeAllOn_of_not_mem {γ : Finset (Sym2 V)} {e : Sym2 V} (he : e ∉ γ)
    (ψ : ConfigSpace (Sym2 V)) : closeAllOn γ ψ e = ψ e := by simp [closeAllOn, he]

omit [Fintype V] in


theorem closeAllOn_setClosed {e : Sym2 V} {γ : Finset (Sym2 V)} (he : e ∉ γ)
    (ψ : ConfigSpace (Sym2 V)) :
    closeAllOn γ (setClosed e ψ) = setClosed e (closeAllOn γ ψ) := by
  funext x
  by_cases hx : x = e
  · subst hx; simp only [setClosed_self, closeAllOn, if_neg he]
  · rw [setClosed_of_ne hx]
    simp only [closeAllOn]
    by_cases hxg : x ∈ γ
    · simp [hxg]
    · rw [if_neg hxg, if_neg hxg, setClosed_of_ne hx]

omit [Fintype V] in


theorem closeAllOn_setOpen {e : Sym2 V} {γ : Finset (Sym2 V)} (he : e ∉ γ)
    (ψ : ConfigSpace (Sym2 V)) :
    closeAllOn γ (setOpen e ψ) = setOpen e (closeAllOn γ ψ) := by
  funext x
  by_cases hx : x = e
  · subst hx; simp only [setOpen_self, closeAllOn, if_neg he]
  · rw [setOpen_of_ne hx]
    simp only [closeAllOn]
    by_cases hxg : x ∈ γ
    · simp [hxg]
    · rw [if_neg hxg, if_neg hxg, setOpen_of_ne hx]


end FK
end StatMech

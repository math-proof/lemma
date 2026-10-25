/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDominationInner.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.DomainMarkov.Part5
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.Inequalities.FKG
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Theorem.StatisticalMechanics.Code.Foundations.StochasticDomination
open scoped BigOperators
open SimpleGraph

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


omit [DecidableRel G.Adj] in


theorem agreesOff_inf {F : Finset (Sym2 V)} {ψ a b : ConfigSpace (Sym2 V)}
    (ha : AgreesOff F ψ a) (hb : AgreesOff F ψ b) : AgreesOff F ψ (a ⊓ b) := by
  intro e he
  show (a e && b e) = ψ e
  rw [ha e he, hb e he]; cases ψ e <;> rfl

omit [DecidableRel G.Adj] in


theorem agreesOff_sup {F : Finset (Sym2 V)} {ψ a b : ConfigSpace (Sym2 V)}
    (ha : AgreesOff F ψ a) (hb : AgreesOff F ψ b) : AgreesOff F ψ (a ⊔ b) := by
  intro e he
  show (a e || b e) = ψ e
  rw [ha e he, hb e he]; cases ψ e <;> rfl

omit [DecidableRel G.Adj] in

theorem condFibre_inf {F : Finset (Sym2 V)} {ψ a b : ConfigSpace (Sym2 V)}
    (ha : a ∈ condFibre F ψ) (hb : b ∈ condFibre F ψ) : a ⊓ b ∈ condFibre F ψ := by
  rw [mem_condFibre] at ha hb ⊢; exact agreesOff_inf ha hb

omit [DecidableRel G.Adj] in

theorem condFibre_sup {F : Finset (Sym2 V)} {ψ a b : ConfigSpace (Sym2 V)}
    (ha : a ∈ condFibre F ψ) (hb : b ∈ condFibre F ψ) : a ⊔ b ∈ condFibre F ψ := by
  rw [mem_condFibre] at ha hb ⊢; exact agreesOff_sup ha hb


end FK
end StatMech

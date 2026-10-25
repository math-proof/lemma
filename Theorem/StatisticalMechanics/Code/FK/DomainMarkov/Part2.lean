/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DomainMarkov.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Def.StatisticalMechanics.Code.FK.DomainMarkov.Part2
open scoped BigOperators


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


omit [DecidableRel G.Adj] in
@[simp] theorem mem_condFibre {F : Finset (Sym2 V)} {ψ ω : ConfigSpace (Sym2 V)} :
    ω ∈ condFibre F ψ ↔ AgreesOff F ψ ω := by
  unfold condFibre; simp

omit [DecidableRel G.Adj] in
theorem self_mem_condFibre (F : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V)) :
    ψ ∈ condFibre F ψ := by rw [mem_condFibre]; exact agreesOff_self F ψ


end FK
end StatMech

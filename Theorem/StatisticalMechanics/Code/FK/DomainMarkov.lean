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
import Instance.StatisticalMechanics.Code.FK.DomainMarkov
open scoped BigOperators


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem agreesOff_self (F : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V)) :
    AgreesOff F ψ ψ := fun _ _ => rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in


theorem agreesOff_symm {F : Finset (Sym2 V)} {ψ ω : ConfigSpace (Sym2 V)}
    (h : AgreesOff F ψ ω) : AgreesOff F ω ψ := fun e he => (h e he).symm

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in


theorem agreesOff_congr {F : Finset (Sym2 V)} {ψ ω : ConfigSpace (Sym2 V)}
    (h : AgreesOff F ψ ω) : AgreesOff F ψ = AgreesOff F ω := by
  funext ρ
  simp only [eq_iff_iff]
  constructor
  · intro hρ e he; rw [hρ e he, h e he]
  · intro hρ e he; rw [hρ e he, ← h e he]


end FK
end StatMech

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
import Def.StatisticalMechanics.Code.FK.DomainMarkov.Part5
open scoped BigOperators


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


theorem condFibre_fkProb_sum {p q : ℝ} (F : Finset (Sym2 V))
    (ψ : ConfigSpace (Sym2 V)) :
    ∑ ρ ∈ condFibre F ψ, fkProb G p q ρ = inducedFkZ G p q F ψ / fkZ G p q := by
  unfold fkProb inducedFkZ
  rw [Finset.sum_div]


theorem condFkProb_eq_inducedFkProb {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (F : Finset (Sym2 V)) (ψ ω : ConfigSpace (Sym2 V)) :
    condFkProb G p q F ψ ω = inducedFkProb G p q F ψ ω := by
  unfold condFkProb inducedFkProb
  rw [condFibre_fkProb_sum]
  unfold fkProb
  rw [div_div_div_cancel_right₀]
  · exact fkZ_ne_zero G hp hp1 hq


theorem condFkProb_sum_eq_one {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (F : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V)) :
    ∑ ω ∈ condFibre F ψ, condFkProb G p q F ψ ω = 1 := by
  rw [Finset.sum_congr rfl
    (fun ω _ => condFkProb_eq_inducedFkProb G hp hp1 hq F ψ ω)]
  exact inducedFkProb_sum_eq_one G hp hp1 hq F ψ


theorem inducedFkZ_congr {p q : ℝ} {F : Finset (Sym2 V)} {ψ ψ' : ConfigSpace (Sym2 V)}
    (h : AgreesOff F ψ ψ') : inducedFkZ G p q F ψ = inducedFkZ G p q F ψ' := by
  unfold inducedFkZ
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext ρ
  simp only [mem_condFibre]
  rw [agreesOff_congr h]

end FK
end StatMech

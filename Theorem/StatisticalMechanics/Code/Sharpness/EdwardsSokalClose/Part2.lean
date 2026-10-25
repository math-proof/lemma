/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/EdwardsSokalClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.EdwardsSokal.Part7
import Theorem.StatisticalMechanics.Code.FK.EsCorrelations.Part4
import Theorem.StatisticalMechanics.Code.FK.Potts.Part6
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Def.StatisticalMechanics.Code.Sharpness.EdwardsSokalClose
open scoped BigOperators

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


theorem esk_esAgreeProb_eq {q : ℕ} (hq : 0 < q) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (x y : V) :
    esAgreeProb G q p x y
      = connProb G p q x y + (1 - connProb G p q x y) / (q : ℝ) := by
  have hqr : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hZpos : 0 < fkZ G p (q:ℝ) := fkZ_pos G hp hp1 hqr
  unfold esAgreeProb
  rw [Finset.sum_congr rfl (fun ω _ => esk_agree_spinsum_fkWeight G hq p ω x y)]
  rw [esZ_eq_fkZ]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun ω : ConfigSpace (Sym2 V) => Connected G ω x y)]
  rw [add_div]
  
  have hconn : (∑ ω ∈ Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => Connected G ω x y),
        (if Connected G ω x y then fkWeight G p (q:ℝ) ω else fkWeight G p (q:ℝ) ω / (q:ℝ)))
        / fkZ G p (q:ℝ)
      = connProb G p q x y := by
    unfold connProb fkProb
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro ω hω
    rw [if_pos (Finset.mem_filter.1 hω).2]
  
  have hdisc : (∑ ω ∈ Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => ¬ Connected G ω x y),
        (if Connected G ω x y then fkWeight G p (q:ℝ) ω else fkWeight G p (q:ℝ) ω / (q:ℝ)))
        / fkZ G p (q:ℝ)
      = (1 - connProb G p q x y) / (q : ℝ) := by
    have hstep : (∑ ω ∈ Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => ¬ Connected G ω x y),
          (if Connected G ω x y then fkWeight G p (q:ℝ) ω else fkWeight G p (q:ℝ) ω / (q:ℝ)))
          / fkZ G p (q:ℝ)
        = (∑ ω ∈ Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => ¬ Connected G ω x y),
            fkProb G p (q:ℝ) ω) / (q:ℝ) := by
      rw [Finset.sum_div, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro ω hω
      rw [if_neg (Finset.mem_filter.1 hω).2]
      unfold fkProb
      ring
    rw [hstep]
    congr 1
    
    have htotal : (∑ ω ∈ Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => Connected G ω x y),
          fkProb G p (q:ℝ) ω)
        + (∑ ω ∈ Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => ¬ Connected G ω x y),
          fkProb G p (q:ℝ) ω)
        = 1 := by
      rw [Finset.sum_filter_add_sum_filter_not]
      exact fkProb_sum_eq_one G hp hp1 hqr
    unfold connProb
    linarith [htotal]
  rw [hconn, hdisc]


theorem esk_pottsCorr_eq {q : ℕ} (hq : 0 < q) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (x y : V) :
    esAgreeProb G q p x y - 1 / (q : ℝ)
      = (((q : ℝ) - 1) / (q : ℝ)) * connProb G p q x y := by
  have hqr : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  rw [esk_esAgreeProb_eq G hq p hp hp1 x y]
  field_simp
  ring


theorem esk_esAgreeProb_eq_pottsAgreeProb (q : ℕ) [NeZero q] (β J : ℝ) (x y : V) :
    esAgreeProb G q (1 - Real.exp (-(β * J))) x y = esk_pottsAgreeProb G q β J x y := by
  unfold esAgreeProb esk_pottsAgreeProb
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro σ _
  rw [← Finset.sum_mul, ← (esFirstMarginal_eq_pottsProb G q β J σ)]
  unfold esFirstMarginal
  ring


theorem esk_edwardsSokal_correlation (q : ℕ) [NeZero q] (β J : ℝ)
    (hβJ : 0 < 1 - Real.exp (-(β * J))) (hβJ1 : 1 - Real.exp (-(β * J)) < 1)
    (x y : V) :
    esk_pottsAgreeProb G q β J x y - 1 / (q : ℝ)
      = (((q : ℝ) - 1) / (q : ℝ))
          * connProb G (1 - Real.exp (-(β * J))) q x y := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  rw [← esk_esAgreeProb_eq_pottsAgreeProb G q β J x y]
  exact esk_pottsCorr_eq G hq (1 - Real.exp (-(β * J))) hβJ hβJ1 x y


theorem esk_pottsCorr_eq_nonvacuous :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V)
      (_ : DecidableRel G.Adj) (q : ℕ) (p : ℝ) (x y : V),
      (0 < q) ∧ (0 < p) ∧ (p < 1) ∧
      (esAgreeProb G q p x y - 1 / (q : ℝ)
        = (((q : ℝ) - 1) / (q : ℝ)) * connProb G p q x y) := by
  refine ⟨Fin 2, inferInstance, inferInstance, ⊤, inferInstance, 2, 1/2, 0, 1,
    by norm_num, by norm_num, by norm_num, ?_⟩
  exact esk_pottsCorr_eq (⊤ : SimpleGraph (Fin 2)) (by norm_num) (1/2)
    (by norm_num) (by norm_num) 0 1

end FK
end StatMech

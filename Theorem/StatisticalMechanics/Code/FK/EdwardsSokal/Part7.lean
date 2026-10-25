/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.Potts.Part6
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Def.StatisticalMechanics.Code.FK.EdwardsSokal.Part7
open scoped BigOperators


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


theorem esSecondMarginal_eq_fkProb (q : ℕ) (p : ℝ) (ω : ConfigSpace (Sym2 V)) :
    esSecondMarginal G q p ω = fkProb G p (q : ℝ) ω := by
  unfold esSecondMarginal fkProb
  rw [esWeight_sum, esZ_eq_fkZ]


theorem esFirstMarginal_eq_pottsProb (q : ℕ) [NeZero q] (β J : ℝ) (σ : V → Fin q) :
    esFirstMarginal G q (1 - Real.exp (-(β * J))) σ = Potts.pottsProb G q β J σ := by
  unfold esFirstMarginal Potts.pottsProb
  rw [esWeight_sum_eq_pottsWeight, esZ_eq_pottsZ]
  rw [mul_div_mul_left _ _ (esFirstConst_pos G β J).ne']


theorem esSecondMarginal_nonneg {q : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 0 < (q : ℝ)) (ω : ConfigSpace (Sym2 V)) :
    0 ≤ esSecondMarginal G q p ω := by
  rw [esSecondMarginal_eq_fkProb]
  exact fkProb_nonneg G hp hp1 hq ω


theorem esSecondMarginal_sum_eq_one {q : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 0 < (q : ℝ)) :
    (∑ ω : ConfigSpace (Sym2 V), esSecondMarginal G q p ω) = 1 := by
  rw [Finset.sum_congr rfl fun ω _ => esSecondMarginal_eq_fkProb G q p ω]
  exact fkProb_sum_eq_one G hp hp1 hq


theorem esFirstMarginal_nonneg {q : ℕ} [NeZero q] (β J : ℝ) (σ : V → Fin q) :
    0 ≤ esFirstMarginal G q (1 - Real.exp (-(β * J))) σ := by
  rw [esFirstMarginal_eq_pottsProb]
  exact Potts.pottsProb_nonneg G q β J σ


theorem esFirstMarginal_sum_eq_one {q : ℕ} [NeZero q] (β J : ℝ) :
    (∑ σ : V → Fin q, esFirstMarginal G q (1 - Real.exp (-(β * J))) σ) = 1 := by
  rw [Finset.sum_congr rfl fun σ _ => esFirstMarginal_eq_pottsProb G q β J σ]
  exact Potts.pottsProb_sum_eq_one G q β J


theorem edwardsSokal_secondMarginal (q : ℕ) (β J : ℝ) (ω : ConfigSpace (Sym2 V)) :
    esSecondMarginal G q (1 - Real.exp (-(β * J))) ω
      = fkProb G (1 - Real.exp (-(β * J))) (q : ℝ) ω :=
  esSecondMarginal_eq_fkProb G q (1 - Real.exp (-(β * J))) ω


theorem edwardsSokal_firstMarginal (q : ℕ) [NeZero q] (β J : ℝ) (σ : V → Fin q) :
    esFirstMarginal G q (1 - Real.exp (-(β * J))) σ = Potts.pottsProb G q β J σ :=
  esFirstMarginal_eq_pottsProb G q β J σ

end FK
end StatMech

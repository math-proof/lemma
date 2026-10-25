/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Tilt.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Def.StatisticalMechanics.Code.FK.Tilt.Part3
open scoped BigOperators


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


theorem fkExpect_tiltPow_pos {p1 p2 q : ℝ} (hp1 : 0 < p1) (hp1' : p1 < 1)
    (hp2 : 0 < p2) (hp2' : p2 < 1) (hq : 0 < q) :
    0 < fkExpect G p1 q (fun ω => tiltFactor p1 p2 ^ openCount G ω) := by
  unfold fkExpect
  apply Finset.sum_pos
  · intro ω _
    exact mul_pos (fkProb_pos G hp1 hp1' hq ω)
      (pow_pos (tiltFactor_pos hp1 hp1' hp2 hp2') _)
  · exact Finset.univ_nonempty


theorem fkZ_tilt {p1 p2 q : ℝ} (hp1 : 0 < p1) (hp1' : p1 < 1)
    (hp2 : 0 < p2) (hp2' : p2 < 1) :
    fkZ G p2 q
      = ((1 - p2) / (1 - p1)) ^ G.edgeFinset.card
        * ∑ ω : ConfigSpace (Sym2 V),
            tiltFactor p1 p2 ^ openCount G ω * fkWeight G p1 q ω := by
  unfold fkZ
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  rw [fkWeight_tilt G hp1 hp1' hp2 hp2' ω]
  ring


theorem fkProb_tilt {p1 p2 q : ℝ} (hp1 : 0 < p1) (hp1' : p1 < 1)
    (hp2 : 0 < p2) (hp2' : p2 < 1) (hq : 0 < q) (ω : ConfigSpace (Sym2 V)) :
    fkProb G p2 q ω
      = tiltFactor p1 p2 ^ openCount G ω * fkProb G p1 q ω
        / fkExpect G p1 q (fun ω => tiltFactor p1 p2 ^ openCount G ω) := by
  have hCpos : (0 : ℝ) < ((1 - p2) / (1 - p1)) ^ G.edgeFinset.card :=
    pow_pos (div_pos (by linarith) (by linarith)) _
  have hC : ((1 - p2) / (1 - p1)) ^ G.edgeFinset.card ≠ 0 := ne_of_gt hCpos
  have hZ1 : fkZ G p1 q ≠ 0 := fkZ_ne_zero G hp1 hp1' hq
  
  have hExp : fkExpect G p1 q (fun ω => tiltFactor p1 p2 ^ openCount G ω)
      = (∑ ω : ConfigSpace (Sym2 V), tiltFactor p1 p2 ^ openCount G ω * fkWeight G p1 q ω)
        / fkZ G p1 q := by
    unfold fkExpect fkProb
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro ω _
    rw [div_mul_eq_mul_div, mul_comm (fkWeight G p1 q ω)]
  rw [fkProb, fkProb, fkZ_tilt G hp1 hp1' hp2 hp2', fkWeight_tilt G hp1 hp1' hp2 hp2' ω,
    hExp]
  field_simp


theorem fkExpect_tilt {p1 p2 q : ℝ} (hp1 : 0 < p1) (hp1' : p1 < 1)
    (hp2 : 0 < p2) (hp2' : p2 < 1) (hq : 0 < q) (X : ConfigSpace (Sym2 V) → ℝ) :
    fkExpect G p2 q X
      = fkExpect G p1 q (fun ω => X ω * tiltFactor p1 p2 ^ openCount G ω)
        / fkExpect G p1 q (fun ω => tiltFactor p1 p2 ^ openCount G ω) := by
  unfold fkExpect
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  rw [fkProb_tilt G hp1 hp1' hp2 hp2' hq ω]
  rw [show fkExpect G p1 q (fun ω => tiltFactor p1 p2 ^ openCount G ω)
    = ∑ ω : ConfigSpace (Sym2 V), fkProb G p1 q ω * tiltFactor p1 p2 ^ openCount G ω from rfl]
  ring

end FK
end StatMech

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Tilt.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Def.StatisticalMechanics.Code.FK.Tilt.Part2
open scoped BigOperators


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


theorem tiltFactor_pos {p1 p2 : ℝ} (hp1 : 0 < p1) (hp1' : p1 < 1)
    (hp2 : 0 < p2) (hp2' : p2 < 1) : 0 < tiltFactor p1 p2 := by
  unfold tiltFactor
  apply div_pos
  · exact mul_pos hp2 (by linarith)
  · exact mul_pos (by linarith) hp1


theorem tiltFactor_lt_one {p1 p2 : ℝ} (hp1 : 0 < p1) (hp1' : p1 < 1)
    (hlt : p2 < p1) : tiltFactor p1 p2 < 1 := by
  unfold tiltFactor
  rw [div_lt_one (mul_pos (by linarith) hp1)]
  nlinarith


theorem pow_tilt_aux {p1 p2 : ℝ} (hp1 : 0 < p1) (hp1' : p1 < 1)
    (hp2 : 0 < p2) (hp2' : p2 < 1) (o c : ℕ) :
    p2 ^ o * (1 - p2) ^ c
      = ((1 - p2) / (1 - p1)) ^ (o + c)
        * tiltFactor p1 p2 ^ o * (p1 ^ o * (1 - p1) ^ c) := by
  unfold tiltFactor
  have h1p1 : (1 - p1) ≠ 0 := by linarith
  have h1p2 : (1 - p2) ≠ 0 := by linarith
  have hp1n : p1 ≠ 0 := ne_of_gt hp1
  rw [div_pow, div_pow, mul_pow, mul_pow, pow_add]
  field_simp
  ring


theorem fkWeight_tilt {p1 p2 q : ℝ} (hp1 : 0 < p1) (hp1' : p1 < 1)
    (hp2 : 0 < p2) (hp2' : p2 < 1) (ω : ConfigSpace (Sym2 V)) :
    fkWeight G p2 q ω
      = ((1 - p2) / (1 - p1)) ^ G.edgeFinset.card
        * tiltFactor p1 p2 ^ openCount G ω * fkWeight G p1 q ω := by
  unfold fkWeight
  rw [edgeProduct_eq_pow G p2 ω, edgeProduct_eq_pow G p1 ω,
    ← openCount_add_closedCount G ω,
    pow_tilt_aux hp1 hp1' hp2 hp2' (openCount G ω) (closedCount G ω)]
  ring


end FK
end StatMech

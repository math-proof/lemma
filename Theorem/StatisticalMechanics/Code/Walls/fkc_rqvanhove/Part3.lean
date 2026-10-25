/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fkc_rqvanhove.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.fkc_rqbdd.Part2
import Theorem.StatisticalMechanics.Code.Walls.fkc_rqbulkfraction
import Def.StatisticalMechanics.Code.Walls.fkc_rqvanhove.Part3
open scoped BigOperators
open SimpleGraph Filter Topology Set

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 2000000


namespace StatMech.Walls

open StatMech StatMech.FK StatMech.Lattice


theorem fkc_f_lower (d : ℕ) (hd : 1 ≤ d) (s q : ℝ) (hq : 1 ≤ q)
    (n : ℕ) (hn : 1 ≤ n) (L : ℝ)
    (hL : Tendsto (fun j => fkc_f d s q (agl_K j)) atTop (nhds L)) :
    ((2 * (n : ℝ) + 1) / (2 * n)) * L
        - (-Real.log (1 - fsc_logistic s)) / (2 * n) ≤ fkc_f d s q n := by
  set c := -Real.log (1 - fsc_logistic s) with hc
  set rfun : ℕ → ℝ := fun j => ((ecz_T n (agl_K j)) ^ d : ℝ)
    * ((boxGraph d n).edgeFinset.card : ℝ)
      / ((boxGraph d (agl_K j)).edgeFinset.card : ℝ) with hrfun
  have hr_tendsto : Tendsto rfun atTop (nhds (2 * (n : ℝ) / (2 * n + 1))) :=
    ecz_bulkFraction_tendsto hd n hn |>.comp agl_K_tendsto_atTop
  have hbound : ∀ j, n ≤ agl_K j →
      fkc_f d s q (agl_K j) ≤ rfun j * fkc_f d s q n + (1 - rfun j) * c := by
    intro j _hj
    have h := fkc_perEdge_vanHove d n (agl_K j) s q hq
      (ecz_box_edge_pos d hd (agl_K_pos j)) (ecz_box_edge_pos d hd hn)
    simpa [hrfun, hc] using h
  have hRHS : Tendsto (fun j => rfun j * fkc_f d s q n + (1 - rfun j) * c) atTop
      (nhds ((2 * (n : ℝ) / (2 * n + 1)) * fkc_f d s q n
        + (1 - 2 * (n : ℝ) / (2 * n + 1)) * c)) :=
    (hr_tendsto.mul tendsto_const_nhds).add
      ((tendsto_const_nhds.sub hr_tendsto).mul tendsto_const_nhds)
  have hKge : ∀ᶠ j in atTop, n ≤ agl_K j := agl_K_tendsto_atTop.eventually_ge_atTop n
  have hLle : L ≤ (2 * (n : ℝ) / (2 * n + 1)) * fkc_f d s q n
      + (1 - 2 * (n : ℝ) / (2 * n + 1)) * c := by
    refine le_of_tendsto_of_tendsto hL hRHS ?_
    filter_upwards [hKge] with j hj using hbound j hj
  have h2n : (0 : ℝ) < 2 * n := by exact_mod_cast (show 0 < 2 * n by omega)
  have h2n1 : (0 : ℝ) < 2 * n + 1 := by positivity
  have hR : (0 : ℝ) < 2 * (n : ℝ) / (2 * n + 1) := by positivity
  have hsolve : (L - (1 - 2 * (n : ℝ) / (2 * n + 1)) * c)
        / (2 * (n : ℝ) / (2 * n + 1)) ≤ fkc_f d s q n := by
    rw [div_le_iff₀ hR]
    linarith
  have halg : (L - (1 - 2 * (n : ℝ) / (2 * n + 1)) * c)
        / (2 * (n : ℝ) / (2 * n + 1))
      = ((2 * (n : ℝ) + 1) / (2 * n)) * L - c / (2 * n) := by
    field_simp
    ring
  rw [halg, hc] at hsolve
  exact hsolve


end StatMech.Walls

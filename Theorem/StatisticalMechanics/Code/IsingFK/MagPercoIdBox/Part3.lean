/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/MagPercoIdBox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.IsingFK.EsInfinite.Part2
import Theorem.StatisticalMechanics.Code.IsingFK.FvES.Part4
import Theorem.StatisticalMechanics.Code.FK.TailLimit.Part2
import Theorem.StatisticalMechanics.Code.Ising.TransitionRegime
import Def.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part2
open MeasureTheory Filter Topology
open scoped BigOperators


namespace StatMech

namespace IsingFK

open StatMech.Ising StatMech.FK StatMech.Lattice StatMech.Percolation

variable {d : ℕ}


theorem fvMagnetization_eq_boxBoundaryConnProfile (d : ℕ) (β : ℝ)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : (0 : ℝ) < 2)
    (hd : 1 ≤ d) {n : ℕ} (hn : 1 ≤ n)
    (hisingBox : fvMagnetization d β n
        = esWiredOnePoint (boxGraph d n) (boxBoundary d n) (0 : Fin 2) p (boxOrigin d n)) :
    fvMagnetization d β n = boxBoundaryConnProfile d hp hp1 hq n := by
  obtain ⟨v₀, hv₀⟩ := boxBoundary_nonempty d n hd hn
  rw [hisingBox, boxBoundaryConnProfile,
    esWiredOnePoint_eq_wiredConnToBdryProb (boxGraph d n) (boxBoundary d n) p
      (boxOrigin d n) v₀ hv₀]


theorem magPercoIdBox_of_fvES_of_fkLim (d : ℕ) (β : ℝ)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : (0 : ℝ) < 2) (hd : 1 ≤ d)
    (hisingBox : ∀ n, 1 ≤ n → fvMagnetization d β n
        = esWiredOnePoint (boxGraph d n) (boxBoundary d n) (0 : Fin 2) p (boxOrigin d n))
    (hfkLimBox : Tendsto (fun n => boxBoundaryConnProfile d hp hp1 hq n) atTop
        (𝓝 (FK.fkTheta d hp hp1 hq (q := 2)))) :
    magnetization d β = FK.fkTheta d hp hp1 hq (q := 2) := by
  
  set b : ℕ → ℝ := fun n => if 1 ≤ n then boxBoundaryConnProfile d hp hp1 hq n
    else fvMagnetization d β n with hb
  have hES : ∀ n, fvMagnetization d β n = b n := by
    intro n
    by_cases hn : 1 ≤ n
    · simp only [hb, if_pos hn]
      exact fvMagnetization_eq_boxBoundaryConnProfile d β hp hp1 hq hd hn (hisingBox n hn)
    · simp only [hb, if_neg hn]
  have hlim : Tendsto b atTop (𝓝 (FK.fkTheta d hp hp1 hq (q := 2))) := by
    
    refine hfkLimBox.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp only [hb, if_pos hn]
  exact magPercoId_of_fvES_of_fkLim d β hp hp1 hq b hES hlim


theorem magPercoIdBox_final (d : ℕ) (hd : 1 ≤ d)
    (hisingBox : ∀ β, 0 < β → ∀ n, 1 ≤ n → fvMagnetization d β n
        = esWiredOnePoint (boxGraph d n) (boxBoundary d n) (0 : Fin 2) (pOfBeta β)
            (boxOrigin d n))
    (hfkLimBox : ∀ β, 0 < β → ∀ (hp : 0 < pOfBeta β) (hp1 : pOfBeta β < 1),
        Tendsto (fun n => boxBoundaryConnProfile d hp hp1 (by norm_num : (0 : ℝ) < 2) n)
          atTop (𝓝 (FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2)))) :
    ∀ β, 0 < β → ∀ (hp : 0 < pOfBeta β) (hp1 : pOfBeta β < 1),
      magnetization d β = FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) := by
  intro β hβ hp hp1
  exact magPercoIdBox_of_fvES_of_fkLim d β hp hp1 (by norm_num) hd
    (hisingBox β hβ) (hfkLimBox β hβ hp hp1)


theorem ising_transition_box (d : ℕ) (hd : 2 ≤ d)
    (hisingBox : ∀ β, 0 < β → ∀ n, 1 ≤ n → fvMagnetization d β n
        = esWiredOnePoint (boxGraph d n) (boxBoundary d n) (0 : Fin 2) (pOfBeta β)
            (boxOrigin d n))
    (hfkLimBox : ∀ β, 0 < β → ∀ (hp : 0 < pOfBeta β) (hp1 : pOfBeta β < 1),
        Tendsto (fun n => boxBoundaryConnProfile d hp hp1 (by norm_num : (0 : ℝ) < 2) n)
          atTop (𝓝 (FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2))))
    (hFKsub : ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 →
      FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
    (hpc1 : FK.fkPc d 2 < 1) :
    ∃ βc : ℝ, 0 < βc ∧
      (∀ β, 0 < β → β < βc → magnetization d β = 0) ∧
      (∀ β, βc < β → 0 < magnetization d β) :=
  Ising.ising_transition_of_fkPc_lt_one d hd
    (magPercoIdBox_final d (le_trans (by norm_num) hd) hisingBox hfkLimBox) hFKsub hpc1


theorem isingBetaC_eq_box (d : ℕ) (hd : 2 ≤ d)
    (hisingBox : ∀ β, 0 < β → ∀ n, 1 ≤ n → fvMagnetization d β n
        = esWiredOnePoint (boxGraph d n) (boxBoundary d n) (0 : Fin 2) (pOfBeta β)
            (boxOrigin d n))
    (hfkLimBox : ∀ β, 0 < β → ∀ (hp : 0 < pOfBeta β) (hp1 : pOfBeta β < 1),
        Tendsto (fun n => boxBoundaryConnProfile d hp hp1 (by norm_num : (0 : ℝ) < 2) n)
          atTop (𝓝 (FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2))))
    (hFKsub : ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 →
      FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
    (hpc1 : FK.fkPc d 2 < 1) :
    IsingFK.betaC (magnetization d) = -(1 / 2) * Real.log (1 - FK.fkPc d 2) :=
  Ising.isingBetaC_eq_of_fkPc_lt_one d hd
    (magPercoIdBox_final d (le_trans (by norm_num) hd) hisingBox hfkLimBox) hFKsub hpc1

end IsingFK
end StatMech

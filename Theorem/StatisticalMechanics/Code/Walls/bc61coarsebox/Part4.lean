/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc61coarsebox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc60upperlines.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc54coarse
import Theorem.StatisticalMechanics.Code.Percolation.CanonForestCount
import Def.StatisticalMechanics.Code.Walls.bc61coarsebox.Part4
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc61_coarseTcount_le_boundary_of_forest (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc61_CoarseForestLeafCount ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R := by
  classical
  obtain ⟨W, _, _, _, G, _, ιT, lamL, hacyc, hmin, hdeg3, hιinj, hlammap, hlaminj⟩ := h
  set Tf := bc61_coarseTrifFinset ω L R with hTf
  set Tw : Finset W := Tf.image ιT with hTw
  have hιinjOn : Set.InjOn ιT Tf := by
    intro y hy z hz hyz
    rw [Finset.mem_coe, bc61_mem_coarseTrifFinset] at hy hz
    exact hιinj y hy.1 hy.2 z hz.1 hz.2 hyz
  have hcardTw : Tw.card = Tf.card := by
    rw [hTw, Finset.card_image_of_injOn hιinjOn]
  have hTwdeg : ∀ w ∈ Tw, 3 ≤ G.degree w := by
    intro w hw
    rw [hTw, Finset.mem_image] at hw
    obtain ⟨y, hyT, rfl⟩ := hw
    rw [bc61_mem_coarseTrifFinset] at hyT
    exact hdeg3 y hyT.1 hyT.2
  
  calc bc61_coarseTcount ω L R = Tf.card := rfl
    _ = Tw.card := hcardTw.symm
    _ ≤ (univ.filter (fun v => 3 ≤ G.degree v)).card := flc2_trifImage_card_le_deg3 G Tw hTwdeg
    _ ≤ (univ.filter (fun v => G.degree v = 1)).card :=
        flc2_forest_internal_le_leaves G hacyc hmin
    _ ≤ boxSV_boundaryCard d R := flc2_leaf_card_le_boundary G R lamL hlammap hlaminj


theorem bc61_coarseTrif_prob_eq_zero (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] (L : ℕ) (bdry : ℕ → ℕ)
    (hexp : ∀ R : ℕ,
      ((boxFinsetBK d R).card : ENNReal) * μ {ω | bc61_IsCoarseTrifurcation ω L 0}
        = ∫⁻ ω, (bc61_coarseTcount ω L R : ENNReal) ∂μ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc61_coarseTcount ω L R ≤ bdry R)
    (hvol : ∀ R, 0 < (boxFinsetBK d R).card)
    (hdens : Filter.Tendsto
      (fun R => (bdry R : ℝ) / ((boxFinsetBK d R).card : ℝ)) Filter.atTop (nhds 0)) :
    μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0 := by
  classical
  set p : ENNReal := μ {ω | bc61_IsCoarseTrifurcation ω L 0} with hp
  have hkey : ∀ R, ((boxFinsetBK d R).card : ENNReal) * p ≤ (bdry R : ENNReal) := by
    intro R
    have hle : ∫⁻ ω, (bc61_coarseTcount ω L R : ENNReal) ∂μ ≤ (bdry R : ENNReal) := by
      calc ∫⁻ ω, (bc61_coarseTcount ω L R : ENNReal) ∂μ
          ≤ ∫⁻ _ω, (bdry R : ENNReal) ∂μ := by
            apply lintegral_mono; intro ω; simp only; exact_mod_cast hbound ω R
        _ = (bdry R : ENNReal) := by rw [lintegral_const]; simp
    rw [hexp R]; exact hle
  have hpfin : p ≠ ⊤ := by rw [hp]; exact (measure_ne_top μ _)
  set pr : ℝ := p.toReal with hpr
  have hprnn : 0 ≤ pr := ENNReal.toReal_nonneg
  have hkeyr : ∀ R, ((boxFinsetBK d R).card : ℝ) * pr ≤ (bdry R : ℝ) := by
    intro R
    have h := hkey R
    have h' : (((boxFinsetBK d R).card : ENNReal) * p).toReal ≤ (bdry R : ENNReal).toReal :=
      ENNReal.toReal_mono (by simp) h
    rw [ENNReal.toReal_mul] at h'
    simpa [ENNReal.toReal_natCast, hpr] using h'
  have hvolr : ∀ R, (0 : ℝ) < ((boxFinsetBK d R).card : ℝ) := fun R => by exact_mod_cast hvol R
  have hle : ∀ R, pr ≤ (bdry R : ℝ) / ((boxFinsetBK d R).card : ℝ) := by
    intro R
    rw [le_div_iff₀ (hvolr R)]
    linarith [hkeyr R]
  have hpr0 : pr ≤ 0 := le_of_tendsto_of_tendsto' tendsto_const_nhds hdens hle
  have hpreq : pr = 0 := le_antisymm hpr0 hprnn
  have hptoreal : p.toReal = 0 := by rw [← hpr]; exact hpreq
  have : p = 0 := (ENNReal.toReal_eq_zero_iff p).mp hptoreal |>.resolve_right hpfin
  rw [hp] at this; exact this


end StatMech.Walls

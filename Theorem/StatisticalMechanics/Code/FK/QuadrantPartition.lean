/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.AdditiveGluing.Part9
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
import Def.StatisticalMechanics.Code.FK.QuadrantPartition
open scoped BigOperators
open SimpleGraph Filter Topology Set MeasureTheory

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000


namespace StatMech

namespace FK

open StatMech.Lattice


variable {U : Type*} [Fintype U] [DecidableEq U] (K₀ : SimpleGraph U) [DecidableRel K₀.Adj]


theorem qp_fkZ_comap_range {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (f : V → U) (g : W → U) (hf : Function.Injective f) (hg : Function.Injective g)
    (hr : Set.range f = Set.range g) (p q : ℝ)
    [DecidableRel (K₀.comap f).Adj] [DecidableRel (K₀.comap g).Adj] :
    fkZ (K₀.comap f) p q = fkZ (K₀.comap g) p q :=
  fsm_fkZ_iso _ _ (qp_comapIsoOfRangeEq K₀ f g hf hg hr) p q


theorem qp_comap_comap {V W : Type*} (g : W → U) (f : V → W) :
    (K₀.comap g).comap f = K₀.comap (g ∘ f) := by
  ext a b; simp only [comap_adj, Function.comp]


theorem qp_fkZ_ge_allClosed {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq1 : 1 ≤ q) :
    (1 - p) ^ G.edgeFinset.card ≤ fkZ G p q := by
  have hterm : (1 - p) ^ G.edgeFinset.card ≤ fkWeight G p q (fun _ => false) := by
    unfold fkWeight edgeProduct
    have hep : (∏ e ∈ G.edgeFinset, (if (fun (_ : Sym2 V) => false) e then p else 1 - p))
        = (1 - p) ^ G.edgeFinset.card := by
      have : (∏ e ∈ G.edgeFinset, (if (fun (_ : Sym2 V) => false) e then p else 1 - p))
          = ∏ _e ∈ G.edgeFinset, (1 - p) := Finset.prod_congr rfl (fun e _ => by simp)
      rw [this, Finset.prod_const]
    rw [hep]
    have hqk : (1 : ℝ) ≤ q ^ numClusters G (fun _ => false) := one_le_pow₀ hq1
    nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ 1 - p) G.edgeFinset.card]
  calc (1 - p) ^ G.edgeFinset.card ≤ fkWeight G p q (fun _ => false) := hterm
    _ ≤ fkZ G p q := by
        unfold fkZ
        exact Finset.single_le_sum (f := fun ω => fkWeight G p q ω)
          (fun ω _ => fkWeight_nonneg G hp hp1 (by linarith) ω) (Finset.mem_univ _)


theorem qp_neglogZ_le_edges {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq1 : 1 ≤ q) :
    -Real.log (fkZ G p q) ≤ (G.edgeFinset.card : ℝ) * (-Real.log (1 - p)) := by
  have h1mp : (0 : ℝ) < 1 - p := by linarith
  have hge := qp_fkZ_ge_allClosed G hp hp1 hq1
  have hpow : (0 : ℝ) < (1 - p) ^ G.edgeFinset.card := pow_pos h1mp _
  have hZ : 0 < fkZ G p q := fkZ_pos G hp hp1 (by linarith)
  have hlog : Real.log ((1 - p) ^ G.edgeFinset.card) ≤ Real.log (fkZ G p q) :=
    Real.log_le_log hpow hge
  rw [Real.log_pow] at hlog
  push_cast at hlog ⊢
  nlinarith [hlog]


end FK
end StatMech

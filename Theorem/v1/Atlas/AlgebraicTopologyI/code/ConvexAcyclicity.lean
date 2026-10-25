/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/ConvexAcyclicity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.AlgebraicTopologyI.code.Section6
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section6
import Def.v1.Atlas.AlgebraicTopologyI.code.ConvexAcyclicity
open Finset BigOperators


namespace AlgebraicTopologyI

noncomputable section

/-- Every coordinate of a point in the standard $m$-simplex is at most $1$, because the
coordinates are nonnegative and sum to $1$. -/
lemma stdSimplex_coord_le_one {m : ℕ} (x : ↥(stdSimplex ℝ (Fin m))) (i : Fin m) :
    x.1 i ≤ 1 := by
  have hi : x.1 i ≤ ∑ j : Fin m, x.1 j :=
    Finset.single_le_sum (fun j _ => x.2.1 j) (Finset.mem_univ i)
  linarith [x.2.2]

/-- The raw cone map `coneRawSimplex` is continuous on the standard $(n+1)$-simplex; the apex
$t_0 = 1$ is handled separately since the factor $(1 - t_0)$ kills the discontinuity of the
`rescaleTail` map there. -/
theorem coneSimplex_continuous (m n : ℕ) (b : ↥(stdSimplex ℝ (Fin m)))
    (σ : C(↥(stdSimplex ℝ (Fin (n + 1))), ↥(stdSimplex ℝ (Fin m)))) :
    Continuous (coneRawSimplex m n b σ) := by

  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro j
  show Continuous (fun t => (coneRawSimplex m n b σ t).1 j)
  rw [continuous_iff_continuousAt]
  intro t

  have hfun_eq : ∀ s : ↥(stdSimplex ℝ (Fin (n + 2))),
      (coneRawSimplex m n b σ s).1 j =
        s.1 0 * b.1 j + (1 - s.1 0) * (σ (rescaleTail n s)).1 j := fun _ => rfl
  by_cases ht : t.1 0 = 1
  ·
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    have h_coord : ContinuousAt (fun s : ↥(stdSimplex ℝ (Fin (n+2))) => s.1 0) t :=
      ((continuous_apply 0).comp continuous_subtype_val).continuousAt
    rw [ContinuousAt, ht, Metric.tendsto_nhds] at h_coord
    filter_upwards [h_coord ε hε] with s hs
    rw [Real.dist_eq] at hs

    have hvalt : (coneRawSimplex m n b σ t).1 j = b.1 j := by
      simp [coneRawSimplex, ht]
    rw [Real.dist_eq, show (coneRawSimplex m n b σ s).1 j - (coneRawSimplex m n b σ t).1 j =
        (1 - s.1 0) * ((σ (rescaleTail n s)).1 j - b.1 j) from by
      rw [hfun_eq, hvalt]; ring, abs_mul]
    have hbnd : |(σ (rescaleTail n s)).1 j - b.1 j| ≤ 1 := by
      rw [abs_le]
      exact ⟨by linarith [(σ (rescaleTail n s)).2.1 j, stdSimplex_coord_le_one b j],
             by linarith [b.2.1 j, stdSimplex_coord_le_one (σ (rescaleTail n s)) j]⟩
    calc |1 - s.1 0| * |(σ (rescaleTail n s)).1 j - b.1 j|
        ≤ |1 - s.1 0| * 1 := mul_le_mul_of_nonneg_left hbnd (abs_nonneg _)
      _ = |1 - s.1 0| := mul_one _
      _ = |s.1 0 - 1| := abs_sub_comm _ _
      _ < ε := hs
  ·
    have hopen : IsOpen {s : ↥(stdSimplex ℝ (Fin (n + 2))) | s.1 0 ≠ 1} :=
      (isOpen_ne.preimage (continuous_apply 0)).preimage continuous_subtype_val

    have h_rescale_at : ContinuousAt (rescaleTail n) t := by
      rw [Topology.IsInducing.subtypeVal.continuousAt_iff]


      have h_loc : ∀ᶠ s in nhds t, (Subtype.val ∘ rescaleTail n) s =
          (fun s : ↥(stdSimplex ℝ (Fin (n+2))) =>
            (fun i : Fin (n+1) => s.1 (Fin.succ i) / (1 - s.1 0))) s := by
        filter_upwards [hopen.mem_nhds ht] with s hs
        simp [Function.comp, rescaleTail, dif_neg hs]

      have h_div : ContinuousAt (fun s : ↥(stdSimplex ℝ (Fin (n+2))) =>
          (fun i : Fin (n+1) => s.1 (Fin.succ i) / (1 - s.1 0))) t := by
        apply continuousAt_pi.mpr
        intro i
        exact ((continuous_apply (Fin.succ i)).comp continuous_subtype_val).continuousAt.div
          ((continuous_const.sub ((continuous_apply 0).comp continuous_subtype_val)).continuousAt)
          (by linarith [stdSimplex_coord_le_one t 0,
              lt_of_le_of_ne (stdSimplex_coord_le_one t 0) ht])
      exact h_div.congr (h_loc.mono (fun s hs => hs.symm))

    have hg : ContinuousAt (fun s : ↥(stdSimplex ℝ (Fin (n+2))) =>
        (σ (rescaleTail n s)).1 j) t :=
      ((continuous_apply j).comp continuous_subtype_val).continuousAt.comp
        (σ.continuous.continuousAt.comp h_rescale_at)
    have ht0 : ContinuousAt (fun s : ↥(stdSimplex ℝ (Fin (n+2))) => s.1 0) t :=
      ((continuous_apply 0).comp continuous_subtype_val).continuousAt
    exact (ht0.mul continuousAt_const).add
      ((continuousAt_const.sub ht0).mul hg) |>.congr
        (Filter.Eventually.of_forall (fun s => (hfun_eq s).symm))

end
end AlgebraicTopologyI

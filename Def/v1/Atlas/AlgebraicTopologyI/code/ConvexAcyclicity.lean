/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/ConvexAcyclicity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.AlgebraicTopologyI.code.Section6
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section6
import Instance.v1.Atlas.AlgebraicTopologyI.code.ConvexAcyclicity
open Finset BigOperators


namespace AlgebraicTopologyI

noncomputable section

/-- Given a point $t$ in the standard $(n+1)$-simplex, drop its first coordinate and rescale the
remaining coordinates by $1/(1-t_0)$ to land in the standard $n$-simplex; this is the inverse to
the front-face inclusion away from the apex $t_0 = 1$. -/
noncomputable def rescaleTail (n : ℕ) (t : ↥(stdSimplex ℝ (Fin (n + 2)))) :
    ↥(stdSimplex ℝ (Fin (n + 1))) := by
  by_cases h : t.1 0 = 1
  · exact ⟨Pi.single 0 1, single_mem_stdSimplex ℝ 0⟩
  · have ht0_lt : t.1 0 < 1 := by
      have h1 : t.1 0 ≤ ∑ i : Fin (n + 2), t.1 i :=
        Finset.single_le_sum (fun i _ => t.2.1 i) (Finset.mem_univ 0)
      exact lt_of_le_of_ne (by linarith [t.2.2]) h
    have h_pos : (1 : ℝ) - t.1 0 > 0 := by linarith
    have htail : ∑ i : Fin (n + 1), t.1 (Fin.succ i) = 1 - t.1 0 := by
      have := t.2.2; rw [Fin.sum_univ_succ] at this; linarith
    refine ⟨fun i => t.1 (Fin.succ i) / (1 - t.1 0), fun i => ?_, ?_⟩
    · exact div_nonneg (t.2.1 (Fin.succ i)) (le_of_lt h_pos)
    · rw [show ∑ i : Fin (n+1), t.1 (Fin.succ i) / (1 - t.1 0) =
          (∑ i : Fin (n+1), t.1 (Fin.succ i)) / (1 - t.1 0) from by
          simp_rw [div_eq_mul_inv]; rw [← Finset.sum_mul]]
      rw [htail, div_self (ne_of_gt h_pos)]

/-- The set-theoretic (pre-continuity) cone map: for a base point $b$ and an $(n+1)$-simplex
$\sigma$ in the standard $m$-simplex, send $t \in \Delta^{n+1}$ to the convex combination
$t_0 \cdot b + (1 - t_0) \cdot \sigma(\text{rescaleTail}(t))$. -/
noncomputable def coneRawSimplex (m n : ℕ) (b : ↥(stdSimplex ℝ (Fin m)))
    (σ : C(↥(stdSimplex ℝ (Fin (n + 1))), ↥(stdSimplex ℝ (Fin m))))
    (t : ↥(stdSimplex ℝ (Fin (n + 2)))) : ↥(stdSimplex ℝ (Fin m)) :=
  let s := rescaleTail n t
  let σs := σ s
  ⟨fun j => t.1 0 * b.1 j + (1 - t.1 0) * σs.1 j,
   (convex_stdSimplex ℝ (Fin m)) b.2 σs.2 (t.2.1 0)
     (by have h1 : t.1 0 ≤ ∑ i : Fin (n+2), t.1 i :=
            Finset.single_le_sum (fun i _ => t.2.1 i) (Finset.mem_univ 0)
         linarith [t.2.2])
     (by linarith)⟩


end
end AlgebraicTopologyI

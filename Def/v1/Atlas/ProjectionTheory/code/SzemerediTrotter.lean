/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/SzemerediTrotter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Instance.v1.Atlas.ProjectionTheory.code.SzemerediTrotter
open Finset Real


namespace SzemerediTrotter

/-- The incidence count $I(X, L) = \#\{(x, \ell) \in X \times L : x \in \ell\}$ between
a finite set of points $X \subset \mathbb{R}^2$ and a finite set of lines $L$. -/
noncomputable def incidenceCount (X : Finset (Fin 2 → ℝ)) (L : Finset Line2) : ℕ := by
  classical
  exact ((X ×ˢ L).filter fun p => p.1 ∈ p.2).card

open Classical in
/-- **Parametric cell-decomposition bound.** For any parameter $s \ge 1$,
$I(X, L) \le |X|^{2/3} |L|^{2/3} + |X|/s + s|L|$. Optimizing in $s$ yields the
Szemerédi--Trotter bound. -/
noncomputable def rRichLines (X : Finset (Fin 2 → ℝ)) (L : Finset Line2) (R : ℕ) :
    Finset Line2 := by
  classical
  exact L.filter (fun l => R ≤ (X.filter (fun x => x ∈ l)).card)

/-- **Bound on the number of $R$-rich lines.** As a corollary of Szemerédi--Trotter:
for $R \ge 2$, $|L_R(X)| \lesssim |X|^2/R^3 + |X|/R$. Here the constant is explicit ($C = 64$). -/
noncomputable def allLinesFromPairs (X : Finset (Fin 2 → ℝ)) : Finset Line2 := by
  classical
  exact (X.offDiag.attach).image (fun ⟨pq, hpq⟩ =>
    { carrier := affineSpan ℝ {pq.1, pq.2}
      dim_eq := by
        have hne : pq.1 ≠ pq.2 := (Finset.mem_offDiag.mp hpq).2.2
        rw [direction_affineSpan, vectorSpan_pair, finrank_span_singleton (vsub_ne_zero.mpr hne)]
      nonempty := ⟨pq.1, subset_affineSpan ℝ _ (Set.mem_insert pq.1 {pq.2})⟩ })

/-- The set of $R$-rich lines among all lines spanned by pairs of points of $X$. -/
noncomputable def allRichLines (X : Finset (Fin 2 → ℝ)) (R : ℕ) : Finset Line2 :=
  rRichLines X (allLinesFromPairs X) R

/-- Bound on the number of $R$-rich lines (among all lines through point pairs of $X$):
$|L_R(X)| \lesssim |X|^2/R^3 + |X|/R$. -/

end SzemerediTrotter

noncomputable section

namespace ProjectionTheory

/-- The orthogonal projection of $p \in \mathbb{R}^2$ in the direction $\theta$,
i.e. $\pi_\theta(p) = p_0 \cos\theta + p_1 \sin\theta$. -/
def projR2 (θ : ℝ) (p : Fin 2 → ℝ) : ℝ :=
  p 0 * Real.cos θ + p 1 * Real.sin θ

/-- The image $\pi_\theta(X) \subset \mathbb{R}$ of a finite point set $X$ under the
direction-$\theta$ projection. -/
def projImageR2 (θ : ℝ) (X : Finset (Fin 2 → ℝ)) : Finset ℝ :=
  X.image (projR2 θ)

/-- The direction-$\theta$ projection $\pi_\theta : \mathbb{R}^2 \to \mathbb{R}$ packaged
as a linear map. -/
def projR2Lin (θ : ℝ) : (Fin 2 → ℝ) →ₗ[ℝ] ℝ where
  toFun := projR2 θ
  map_add' := fun x y => by simp [projR2]; ring
  map_smul' := fun c x => by simp [projR2]; ring

end ProjectionTheory
end

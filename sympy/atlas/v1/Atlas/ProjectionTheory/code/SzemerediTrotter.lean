/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/SzemerediTrotter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Finset Real

namespace SzemerediTrotter

/-- A line in $\mathbb{R}^2$: a $1$-dimensional non-empty affine subspace of $\mathbb{R}^2$. -/
structure Line2 where
  carrier : AffineSubspace ℝ (Fin 2 → ℝ)
  dim_eq : Module.finrank ℝ carrier.direction = 1
  nonempty : (carrier : Set (Fin 2 → ℝ)).Nonempty

/-- Membership of a point in a `Line2`: $p \in \ell$ iff $p$ belongs to the underlying
affine subspace. -/
instance : Membership (Fin 2 → ℝ) Line2 where
  mem l p := p ∈ l.carrier

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

/-- The projection map $\pi_\theta : \mathbb{R}^2 \to \mathbb{R}$ is surjective. -/
lemma projR2Lin_surjective (θ : ℝ) : Function.Surjective (projR2Lin θ) := by
  intro y
  refine ⟨![y * Real.cos θ, y * Real.sin θ], ?_⟩
  simp only [projR2Lin, projR2, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  have key : y * Real.cos θ * Real.cos θ + y * Real.sin θ * Real.sin θ = y := by
    have : y * Real.cos θ * Real.cos θ + y * Real.sin θ * Real.sin θ
        = y * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring
    rw [this, Real.cos_sq_add_sin_sq, mul_one]
  linarith [key]

/-- For $\theta \in [0, \pi)$, the kernel of $\pi_\theta$ is a $1$-dimensional subspace
of $\mathbb{R}^2$, so its fibers are honest lines. -/
lemma projR2Lin_ker_finrank (θ : ℝ) (hθ : 0 ≤ θ ∧ θ < Real.pi) :
    Module.finrank ℝ (LinearMap.ker (projR2Lin θ)) = 1 := by
  have h_rank_ker := (projR2Lin θ).finrank_range_add_finrank_ker
  have h_total : Module.finrank ℝ (Fin 2 → ℝ) = 2 := by simp
  rw [h_total] at h_rank_ker
  suffices h_range : Module.finrank ℝ (LinearMap.range (projR2Lin θ)) = 1 by omega
  have h_surj : LinearMap.range (projR2Lin θ) = ⊤ :=
    LinearMap.range_eq_top.mpr (projR2Lin_surjective θ)
  rw [h_surj]; simp [Module.finrank_self]

/-- The line through $p_0$ in direction $\theta \in [0, \pi)$: the fiber of $\pi_\theta$
passing through $p_0$, packaged as a `Line2`. -/
def mkProjLine (θ : ℝ) (hθ : 0 ≤ θ ∧ θ < Real.pi) (p₀ : Fin 2 → ℝ) :
    SzemerediTrotter.Line2 where
  carrier := AffineSubspace.mk' p₀ (LinearMap.ker (projR2Lin θ))
  dim_eq := by rw [AffineSubspace.direction_mk']; exact projR2Lin_ker_finrank θ hθ
  nonempty := ⟨p₀, by simp [AffineSubspace.mem_mk', sub_self]⟩

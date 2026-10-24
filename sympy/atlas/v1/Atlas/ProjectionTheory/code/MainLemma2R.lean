/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MainLemma2R.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

noncomputable section

open MeasureTheory Metric Set Finset
open scoped Classical InnerProductSpace

namespace ProjectionTheory

/-- The perpendicular direction in $\mathbb{R}^2$: rotates a vector $(e_0, e_1)$ to
$(-e_1, e_0)$. -/
def perpDir (e : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i =>
    if i = (0 : Fin 2) then -(EuclideanSpace.equiv (Fin 2) ℝ e 1)
    else EuclideanSpace.equiv (Fin 2) ℝ e 0)

/-- The rectangle in $\mathbb{R}^2$ centered at `center` with major axis along `dir`,
of half-length `halfLength` along `dir` and half-width `halfWidth` along `perpDir dir`. -/
def rectangleSet (center : EuclideanSpace ℝ (Fin 2))
    (dir : EuclideanSpace ℝ (Fin 2)) (halfWidth halfLength : ℝ) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | |⟪x - center, dir⟫_ℝ| ≤ halfLength ∧
       |⟪x - center, perpDir dir⟫_ℝ| ≤ halfWidth}

/-- A $1 \times R$ tube in $\mathbb{R}^2$: a long, thin rectangle with unit direction
vector, length `R ≥ 1`, and width $1$. -/
structure Tube where
  R : ℝ
  center : EuclideanSpace ℝ (Fin 2)
  direction : EuclideanSpace ℝ (Fin 2)
  direction_unit : ‖direction‖ = 1
  hR : 1 ≤ R

/-- Realize a `Tube` as the set $\{x \in \mathbb{R}^2 : |\langle x - c, d\rangle| \leq R/2,
\ |\langle x - c, d^\perp\rangle| \leq 1/2\}$. -/
def Tube.asSet (T : Tube) : Set (EuclideanSpace ℝ (Fin 2)) :=
  rectangleSet T.center T.direction (1/2) (T.R/2)

/-- The two-dimensional Fourier transform $\hat f(\xi) = \int f(x) e^{-2\pi i \langle x,
\xi\rangle}\, dx$ of a real-valued function on $\mathbb{R}^2$, returning a complex value. -/
def fourierTransformR2 (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (ξ : EuclideanSpace ℝ (Fin 2)) : ℂ :=
  VectorFourier.fourierIntegral Real.fourierChar volume
    (innerₗ (EuclideanSpace ℝ (Fin 2))) (fun x => (f x : ℂ)) ξ

/-- The set of dyadic scales between $1$ and $R$: $\{2^k : k \in \mathbb{N}, 1 \leq 2^k \leq R\}$. -/
def dyadicScales (R : ℝ) : Set ℝ :=
  {r : ℝ | ∃ k : ℕ, r = 2 ^ k ∧ 1 ≤ r ∧ r ≤ R}

/-- A collection of $1 \times R$ tubes in $\mathbb{R}^2$ together with smooth bump
functions $\psi_i$ adapted to each tube and a (compactly supported) Fourier bound.
This is the data $f = \sum_T \psi_T$ used in the real-version Main Lemma 2R. -/
structure TubeCollection where
  R : ℝ
  hR : 1 ≤ R
  ι : Type
  [hι : Fintype ι]
  tubes : ι → Tube
  tubes_scale : ∀ i, (tubes i).R = R
  ψ : ι → (EuclideanSpace ℝ (Fin 2) → ℝ)
  ψ_smooth : ∀ i, ContDiff ℝ ⊤ (ψ i)
  ψ_integrable : ∀ i, Integrable (ψ i) volume
  fourierSupportBound : ℝ
  ψ_fourier_compact_support : ∀ i, ∀ ξ : EuclideanSpace ℝ (Fin 2),
    ‖ξ‖ > fourierSupportBound → fourierTransformR2 (ψ i) ξ = 0

/-- The index type of a `TubeCollection` is a `Fintype`. -/
instance (S : TubeCollection) : Fintype S.ι := S.hι

/-- The aggregated tube sum $f(x) = \sum_i \psi_i(x)$. -/
def TubeCollection.tubeSum (S : TubeCollection) (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  ∑ i : S.ι, S.ψ i x

/-- The number of tubes in `S` contained in the $r \times R$ rectangle with center `c`
and direction `d`. -/
def TubeCollection.countContained (S : TubeCollection) (r : ℝ)
    (c : EuclideanSpace ℝ (Fin 2)) (d : EuclideanSpace ℝ (Fin 2)) : ℕ :=
  (Finset.univ.filter fun j =>
    (S.tubes j).asSet ⊆ rectangleSet c d r S.R).card

/-- The multiplicity at scale $r$: the maximum, over all $r \times R$ rectangles, of the
number of tubes of `S` contained in that rectangle. -/
def TubeCollection.multiplicity (S : TubeCollection) (r : ℝ) : ℕ :=
  sSup {n : ℕ | ∃ (c : EuclideanSpace ℝ (Fin 2)) (d : EuclideanSpace ℝ (Fin 2)),
    n = S.countContained r c d}

/-- A frequency decomposition $f = \sum_{r} f_r$ of the tube sum into pieces with
Fourier support in $\{|\xi| \leq 1/r\}$, satisfying a near-orthogonality $L^2$ bound. -/
structure FrequencyDecomposition (S : TubeCollection) where
  f_r : ℝ → (EuclideanSpace ℝ (Fin 2) → ℝ)
  scales : Finset ℝ
  scales_range : ∀ r ∈ scales, r ∈ dyadicScales S.R
  sum_eq : ∀ x, S.tubeSum x = ∑ r ∈ scales, f_r r x
  fourier_support : ∀ r ∈ scales, ∀ ξ : EuclideanSpace ℝ (Fin 2),
    ‖ξ‖ > 1 / r → fourierTransformR2 (f_r r) ξ = 0
  near_orthogonality : ∃ (C_orth : ℝ), 0 < C_orth ∧
    ∑ r ∈ scales, ∫ x, (f_r r x) ^ 2 ≤ C_orth * ∫ x, (S.tubeSum x) ^ 2

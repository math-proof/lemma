/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MainLemmaReal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Structure.v1.Atlas.ProjectionTheory.code.MainLemmaReal
open MeasureTheory Metric Set


noncomputable section

namespace FrequencyDecomposition

/-- Realize a tube $T$ as the rectangle of half-length $R/2$ along direction $\theta$
and half-width $1/2$ along the perpendicular. -/
def Tube.toSet (T : Tube) : Set ℝ2 :=
  {x | let diff := (EuclideanSpace.equiv (Fin 2) ℝ) (x - T.center)
       let θ := T.direction
       let longCoord := diff 0 * Real.cos θ + diff 1 * Real.sin θ
       let shortCoord := -diff 0 * Real.sin θ + diff 1 * Real.cos θ
       |longCoord| ≤ T.R / 2 ∧ |shortCoord| ≤ 1 / 2}

/-- Realize a `WideTube` as the corresponding rectangle in $\mathbb{R}^2$. -/
def WideTube.toSet (W : WideTube) : Set ℝ2 :=
  {x | let diff := (EuclideanSpace.equiv (Fin 2) ℝ) (x - W.center)
       let θ := W.direction
       let longCoord := diff 0 * Real.cos θ + diff 1 * Real.sin θ
       let shortCoord := -diff 0 * Real.sin θ + diff 1 * Real.cos θ
       |longCoord| ≤ W.halfLength ∧ |shortCoord| ≤ W.halfWidth}

/-- A tube $T$ is contained in a wide tube $W$ if the rectangle of $T$ lies inside $W$. -/
def Tube.containedIn (T : Tube) (W : WideTube) : Prop :=
  T.toSet ⊆ W.toSet

/-- The dyadic scales up to $R$: $\{2^k : k \in \mathbb{N}, 2^k \leq R\}$ as a `Finset`. -/
def dyadicRange (R : ℝ) : Finset ℝ :=
  ((Finset.range (Nat.log 2 ⌊R⌋₊ + 1)).image (fun k => (2 : ℝ) ^ k)).filter (· ≤ R)

open Classical in
/-- Tube covering number $N_\mathcal{T}(r) = \max_W |\{T \in \mathcal{T} : T \subseteq W\}|$,
maximizing over $r \times R$ wide tubes $W$. -/
def tubeCoveringNumber (𝒯 : Finset Tube) (R r : ℝ) : ℕ :=
  sSup {n : ℕ | ∃ W : WideTube, W.halfWidth = r ∧ W.halfLength = R ∧
    n = (𝒯.filter (fun T => T.containedIn W)).card}

/-- The $L^2$ norm squared $\|f\|_{L^2}^2 = \int_{\mathbb{R}^2} |f(x)|^2\, dx$. -/
def l2NormSq (f : ℝ2 → ℂ) : ℝ :=
  ∫ x, ‖f x‖ ^ 2

/-- The support of the Fourier transform of `f` in $\mathbb{R}^2$. -/
def fourierSupport (f : ℝ2 → ℂ) : Set ℝ2 :=
  Function.support (FourierTransform.fourier f)

/-- The cumulative frequency projection $P_{\leq 1/r} f$: the inverse Fourier transform
of $\hat f(\xi) \cdot \mathbf{1}_{|\xi| \leq 1/r}$. -/
def cumulativeFreqProj (f : ℝ2 → ℂ) (r : ℝ) : ℝ2 → ℂ :=
  FourierTransformInv.fourierInv
    (fun ξ => (FourierTransform.fourier f) ξ * (if dist ξ 0 ≤ 1 / r then (1 : ℂ) else 0))

/-- The $k$-th Littlewood–Paley piece of $f$ at depth $K$:
$\Delta_k f = P_{\leq 2^{-k}} f - P_{\leq 2^{-(k+1)}} f$ for $k < K$, and the final
endpoint $P_{\leq 2^{-K}} f$ when $k = K$ (with $f$ itself when $k = 0$). -/
def littlewoodPaleyPieceK (f : ℝ2 → ℂ) (K k : ℕ) (x : ℝ2) : ℂ :=
  let g : ℕ → ℂ := fun j => if j = 0 then f x else cumulativeFreqProj f ((2 : ℝ) ^ j) x
  if k < K then g k - g (k + 1) else g K

/-- The Littlewood–Paley piece $f_r$ at dyadic scale $r$ of the tube sum
$f = \sum_T \varphi_T$, indexed by the integer $\log_2 r$. -/
def littlewoodPaleyPiece (𝒯 : Finset Tube) (φ : Tube → ℝ2 → ℂ) (R r : ℝ) : ℝ2 → ℂ :=
  let f : ℝ2 → ℂ := fun x => ∑ T ∈ 𝒯, φ T x
  fun x => littlewoodPaleyPieceK f (Nat.log 2 ⌊R⌋₊) (Nat.log 2 ⌊r⌋₊) x

end FrequencyDecomposition
end

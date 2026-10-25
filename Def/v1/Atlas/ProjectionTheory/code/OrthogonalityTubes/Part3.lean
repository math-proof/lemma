/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/OrthogonalityTubes.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Structure.v1.Atlas.ProjectionTheory.code.OrthogonalityTubes.Part2


noncomputable section

namespace OrthogonalityTubes

open MeasureTheory

/-- The underlying point set of a `Rectangle`: a $w \times l$ rectangle centred at
`rect.center` with axis `rect.direction`. -/
def Rectangle.carrier {w l : ℝ} (rect : Rectangle w l) : Set (EuclideanSpace ℝ (Fin 2)) :=
  rectangleCarrier rect.center rect.direction w l

/-- A tube `T` is *contained in* a rectangle `rect` if its carrier is a subset of the
rectangle's carrier. -/
def Tube.containedIn {R : ℝ} (T : Tube R) {w l : ℝ} (rect : Rectangle w l) : Prop :=
  T.carrier ⊆ rect.carrier

/-- The standard bilinear pairing $(v, w) \mapsto \langle v, w\rangle$ on
$\mathbb{R}^2$, packaged as a continuous bilinear map (used to define the Fourier
transform on $\mathbb{R}^2$). -/
def stdBilinR2 : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℝ where
  toFun v := {
    toFun := fun w => @inner ℝ _ _ v w
    map_add' := fun w₁ w₂ => by simp [inner_add_right]
    map_smul' := fun c w => by simp [inner_smul_right]
  }
  map_add' := fun v₁ v₂ => by ext w; simp [inner_add_left]
  map_smul' := fun c v => by ext w; simp [inner_smul_left]

/-- The Fourier transform on $\mathbb{R}^2$:
$\widehat f(\xi) = \int_{\mathbb{R}^2} f(x)\, e^{-2\pi i \langle x, \xi\rangle}\, dx$. -/
def fourierTransformR2 (f : EuclideanSpace ℝ (Fin 2) → ℂ) :
    EuclideanSpace ℝ (Fin 2) → ℂ :=
  VectorFourier.fourierIntegral Real.fourierChar volume stdBilinR2 f

/-- The frequency annulus at scale $r$: $\{\xi : r^{-1}/2 \le \|\xi\| \le 2 r^{-1}\}$. -/
def freqAnnulus (r : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {ξ | r⁻¹ / 2 ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 2 * r⁻¹}

/-- The frequency-localised wave packet $\phi_{T, r}$ associated to a tube $T$ at scale $r$:
a function whose Fourier transform is concentrated in an angular cap of width $\sim r/R$
around the direction of $T$. -/
def freqAngularCap (R r : ℝ) (T : Tube R) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {ξ | ξ ∈ freqAnnulus r ∧ ‖ξ - (‖ξ‖ • T.direction)‖ ≤ (r / (3 * R)) * ‖ξ‖}

/-- Angular Fourier support of the tube wave packet: $\widehat{\phi_{T, r}}$ vanishes outside
the frequency angular cap of $T$. -/
def l2Inner (f g : EuclideanSpace ℝ (Fin 2) → ℂ) : ℂ :=
  ∫ x, f x * starRingEnd ℂ (g x) ∂volume

/-- A surrogate for the angle between two tubes: $\|T_1.\text{direction} -
T_2.\text{direction}\|$ (which is comparable to $|\sin \theta|$ for the actual angle
$\theta$ between the directions when both are unit vectors). -/
def Tube.angle {R : ℝ} (T₁ T₂ : Tube R) : ℝ :=
  ‖T₁.direction - T₂.direction‖

end OrthogonalityTubes
end

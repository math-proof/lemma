/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheWordAlgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAmplitudeExchange
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheWordAlgebra.Part2


namespace StatMech.FrontierD

noncomputable section

def sixVertexCoordinateBetheIntWave {n : ℕ} (c : ℝ)
    (p : Fin n → ℝ) (x : Fin n → ℤ) : ℂ :=
  ∑ σ, sixVertexBetheAmplitude c p σ *
    sixVertexBetheIntMonomial p σ x


def sixVertexBetheWordEdgeFactor {n : ℕ} (c : ℝ)
    (z : Fin (n + 1) → ℂ) (σ : Equiv.Perm (Fin (n + 1)))
    (w : Finset (Fin (n + 1))) (i : Fin (n + 1)) : ℂ :=
  if i ∈ w then
    if finRotate (n + 1) i ∈ w then
      sixVertexBetheL c (z (σ (finRotate (n + 1) i)))
    else 1
  else if finRotate (n + 1) i ∈ w then
    sixVertexBetheM c (z (σ i)) *
      sixVertexBetheL c (z (σ (finRotate (n + 1) i))) - 1
  else sixVertexBetheM c (z (σ i))


def sixVertexBetheWordCoefficient {n : ℕ} (c : ℝ)
    (z : Fin (n + 1) → ℂ) (σ : Equiv.Perm (Fin (n + 1)))
    (w : Finset (Fin (n + 1))) : ℂ :=
  ∏ i, sixVertexBetheWordEdgeFactor c z σ w i


def sixVertexBetheWordCoefficientRemainder {n : ℕ} (c : ℝ)
    (z : Fin (n + 1) → ℂ) (σ : Equiv.Perm (Fin (n + 1)))
    (w : Finset (Fin (n + 1))) (a : Fin (n + 1)) : ℂ :=
  ∏ i ∈ Finset.univ.erase a, sixVertexBetheWordEdgeFactor c z σ w i


def sixVertexBetheWordMonomial {n : ℕ} (N : ℕ)
    (z : Fin (n + 1) → ℂ) (σ : Equiv.Perm (Fin (n + 1)))
    (x : Fin (n + 1) → ℤ) (w : Finset (Fin (n + 1))) : ℂ :=
  ∏ i, if i ∈ w then
    z (σ i) ^ (sixVertexBetheShiftCoordinates N x i)
  else z (σ i) ^ (x i)

end
end StatMech.FrontierD

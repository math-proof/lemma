module
public import Mathlib
public import Mathlib.Analysis.Matrix.Normed
public import Theorem.StatisticalMechanics.Code.Onsager.DetWalkExp
public import Theorem.StatisticalMechanics.Code.Onsager.KWSpinFourier.Part3
public import Theorem.StatisticalMechanics.Code.Onsager.KWSpectral


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpectral.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Onsager

noncomputable def ons_KWconvergenceRadius (L : ℕ) [NeZero L] : ℝ :=
  (Fintype.card (ons_Dart L) : ℝ)⁻¹

end StatMech.Onsager

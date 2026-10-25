/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Fintype.Fin
import Mathlib.Order.Hom.PowersetCard
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertex.Part6
open Finset Matrix


namespace StatMech.FrontierD

noncomputable def sixVertexSectorTopIndex (N n : ℕ) (hn : n ≤ N) :
    Fin (Fintype.card (SixVertexSector N n)) := by
  letI : Nonempty (SixVertexSector N n) := sixVertexSector_nonempty hn
  exact ⟨0, Fintype.card_pos⟩


noncomputable def sixVertexSectorTopEigenvalue (N n : ℕ) (hn : n ≤ N)
    (c : ℝ) : ℝ :=
  (sixVertexSectorTransfer_isHermitian N n c).eigenvalues₀
    (sixVertexSectorTopIndex N n hn)


end StatMech.FrontierD

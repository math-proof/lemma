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
import Def.StatisticalMechanics.Code.FrontierD.SixVertex.Part8
open Finset Matrix


namespace StatMech.FrontierD

theorem sixVertexSectorTopEigenvalue_ge (N n : ℕ) (hn : n ≤ N) (c : ℝ)
    (i : Fin (Fintype.card (SixVertexSector N n))) :
    (sixVertexSectorTransfer_isHermitian N n c).eigenvalues₀ i ≤
      sixVertexSectorTopEigenvalue N n hn c := by
  apply (sixVertexSectorTransfer_isHermitian N n c).eigenvalues₀_antitone
  change (sixVertexSectorTopIndex N n hn).val ≤ i.val
  exact Nat.zero_le _


theorem sixVertexSectorTop_hasEigenvalue (N n : ℕ) (hn : n ≤ N) (c : ℝ) :
    Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (sixVertexSectorTransfer N n c))
      (sixVertexSectorTopEigenvalue N n hn c) := by
  exact LinearMap.IsSymmetric.hasEigenvalue_eigenvalues
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (sixVertexSectorTransfer_isHermitian N n c))
    finrank_euclideanSpace (sixVertexSectorTopIndex N n hn)


end StatMech.FrontierD

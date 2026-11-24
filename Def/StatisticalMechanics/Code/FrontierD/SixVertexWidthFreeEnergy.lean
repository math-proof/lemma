module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFiniteTorus.Part5
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFreeEnergy
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexWidthFreeEnergy
open Finset Matrix Filter Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexWidthFreeEnergy.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable def sixVertexWidthSectorTopEigenvalue
    (N : ℕ) (c : ℝ) (n : Fin (N + 1)) : ℝ :=
  sixVertexSectorTopEigenvalue N n (sixVertexWidthSectorIndex_le N n) c


noncomputable def sixVertexWidthTopEigenvalue (N : ℕ) (c : ℝ) : ℝ :=
  (Finset.univ.image (sixVertexWidthSectorTopEigenvalue N c)).max'
    (Finset.image_nonempty.mpr Finset.univ_nonempty)

end StatMech.FrontierD

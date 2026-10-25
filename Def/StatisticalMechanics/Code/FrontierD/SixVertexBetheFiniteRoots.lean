/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFiniteRoots.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheVariational.Part12
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheScattering.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCoordinateBethe.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheThermodynamicReduction.Part5


namespace StatMech.FrontierD

noncomputable section

def sixVertexHalfFilledBetheRoots
    {c : ℝ} (hc : 2 < c) (k : ℕ) :
    Fin ((k + 1) + (k + 1)) → ℝ :=
  sixVertexChosenBetheSolution hc (N := sixVertexFourWidth 0 k)
    (n := (k + 1) + (k + 1)) (by unfold sixVertexFourWidth; omega)


def sixVertexPositiveHalfBetheRoots
    {c : ℝ} (hc : 2 < c) (k : ℕ) : Fin (k + 1) → ℝ :=
  fun j => sixVertexHalfFilledBetheRoots hc k (Fin.natAdd (k + 1) j)


def sixVertexPositiveHalfBetheRootFamily
    {c : ℝ} (hc : 2 < c) : SixVertexSymmetricHalfFilledRoots :=
  fun k => sixVertexPositiveHalfBetheRoots hc k

end
end StatMech.FrontierD

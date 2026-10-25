/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexParticleHole.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPerron.Part9
import Def.StatisticalMechanics.Code.FrontierD.SixVertexParticleHole.Part4
open Finset Matrix


namespace StatMech.FrontierD

theorem sixVertexSectorTopEigenvalue_congr_index
    {N a b : ℕ} (hab : a = b) (ha : a ≤ N) (hb : b ≤ N) (c : ℝ) :
    sixVertexSectorTopEigenvalue N a ha c =
      sixVertexSectorTopEigenvalue N b hb c := by
  subst b
  rfl


theorem sixVertexLambda_particleHole (N r : ℕ) (hN : Even N)
    (hr : r ≤ N / 2) (c : ℝ) :
    sixVertexLambdaNeg N r hN hr c = sixVertexLambda N r hN hr c := by
  let hn : N / 2 - r ≤ N := (Nat.sub_le _ _).trans (Nat.div_le_self N 2)
  have h := sixVertexSectorTopEigenvalue_particleHole hn c
  obtain ⟨k, hk⟩ := hN
  subst N
  have hidx : k + k - ((k + k) / 2 - r) = (k + k) / 2 + r := by omega
  unfold sixVertexLambdaNeg sixVertexLambda
  convert h using 1
  exact sixVertexSectorTopEigenvalue_congr_index hidx.symm _ _ c

end StatMech.FrontierD

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVandermonde.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnisotropyRoots.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSpectralIsolation
import Mathlib.LinearAlgebra.Vandermonde
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheVandermonde.Part2
open Finset Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

theorem tendsto_sixVertexHalfFilledNormalizedAmplitude (k : Nat)
    (sigma : Equiv.Perm (Fin ((k + 1) + (k + 1)))) :
    Tendsto (sixVertexHalfFilledNormalizedAmplitude k · sigma) atTop
      (nhds ((((Equiv.Perm.sign sigma : Int) : Complex)) *
        ∏ i, ∏ _j ∈ Finset.Ioi i,
          sixVertexHalfFilledLimitingPhase k (sigma i))) := by
  unfold sixVertexHalfFilledNormalizedAmplitude
  apply tendsto_const_nhds.mul
  apply tendsto_finsetProd Finset.univ
  intro i _
  apply tendsto_finsetProd (Finset.Ioi i)
  intro j _
  exact tendsto_sixVertexNormalizedBethePairFactorAt k (sigma i) (sigma j)

theorem tendsto_sixVertexHalfFilledOddMonomial (k : Nat)
    (sigma : Equiv.Perm (Fin ((k + 1) + (k + 1)))) :
    Tendsto
      (fun c => sixVertexBetheMonomial
        (fun j => sixVertexHalfFilledBetheRootAt k j c) sigma
        (sixVertexAlternatingOddSector
          (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) (by
            unfold sixVertexFourWidth
            omega)))
      atTop
      (nhds (∏ i, sixVertexHalfFilledLimitingPhase k (sigma i) ^
        (2 * i.val + 1))) := by
  unfold sixVertexBetheMonomial
  simp only [sixVertexSectorPosition_alternatingOdd_apply_val]
  apply tendsto_finsetProd Finset.univ
  intro i _
  exact (tendsto_sixVertexHalfFilledBethePhaseAt k (sigma i)).pow
    (2 * i.val + 1)


end
end StatMech.FrontierD

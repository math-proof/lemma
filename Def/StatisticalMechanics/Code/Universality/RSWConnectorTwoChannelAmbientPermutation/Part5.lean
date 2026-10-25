/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelAmbientPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelStaticCutEndpoint
import Theorem.StatisticalMechanics.Code.Universality.RSWSequentialStoppedConditionalLaw.Part16
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelAmbientPermutation.Part6
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_twoChannelIndexedAmbientFailureEmbedding
    {n : Int} {I : Type*} (pair : I → RlcDiagonalPathPair n)
    (hfaith : ∀ i, RlcBookFaithfulTracePair (pair i).1 (pair i).2)
    (hstatic : ∀ i, RlcTwoChannelFullPhysicalStaticCutIntersection
      (pair i).1 (pair i).2 (hfaith i))
    (hrecover : RlcTwoChannelIndexedAmbientCollisionRecovery
      pair hfaith hstatic) :
    RlcTwoChannelIndexedSelectedFailure I pair ↪
      ConfigSpace (Sym2 (RlcConnectorVertex n)) where
  toFun := rlc_twoChannelIndexedAmbientFailureMap pair hfaith hstatic
  inj' := by
    intro x y hxy
    have hindex : x.index = y.index := hrecover x y hxy
    cases x with
    | mk ix rho hselected hfailure =>
      cases y with
      | mk iy sigma hselected' hfailure' =>
        dsimp only at hindex
        subst iy
        simp only [rlc_twoChannelIndexedAmbientFailureMap] at hxy
        have hlocal :
            (⟨rho, hfailure⟩ :
              {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) //
                rho ∉ rlc_finiteTwoChannelConnectorEvent
                  (pair ix).1 (pair ix).2}) =
            ⟨sigma, hfailure'⟩ :=
          (rlc_twoChannelFullPhysicalAmbientFailureEmbedding
            (hfaith ix) (hstatic ix)).injective hxy
        cases hlocal
        rfl

end
end StatMech.Universality

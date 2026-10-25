/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/GrothendieckGroupO.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.ProjectiveFunctors.Part7
import Lemma.Int.IsDirectSummand
import Lemma.Finset.EqMul_Mul.of.In_SimpleReflections
import Def.v1.Atlas.LieGroups.code.HeckeKL.Part9
import Structure.v1.Atlas.LieGroups.code.GrothendieckGroupO
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false


noncomputable section

open scoped TensorProduct

open ProjectiveFunctors Classical

universe u

variable {R : Type u} [CommRing R]

variable {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]

def AdjointPairDataWeak.toAdjointPairData
    (adj : AdjointPairDataWeak (R := R) (𝔤 := 𝔤))
    (hF : IsProjectiveFunctor adj.F)
    (hFv : IsProjectiveFunctor adj.Fv)
    (hDim : ∀ {Δ : TriangularDecomposition R 𝔤}
      (KO : GrothendieckGroupData Δ)
      (ip : KO.InnerProductData)
      (fF fFv : InducedMapData KO)
      (_ : fF.F = adj.F) (_ : fFv.F = adj.Fv)
      (lam mu : Δ.𝔥 →ₗ[R] R),
      ip.pairing (fF.mapKO (KO.delta lam)) (KO.delta mu) =
      ip.pairing (fFv.mapKO (KO.delta mu)) (KO.delta lam)) :
    AdjointPairData (R := R) (𝔤 := 𝔤) :=
  { F := adj.F
    Fv := adj.Fv
    hF := hF
    hFv := hFv
    adjunction_fwd := adj.adjunction_fwd
    adjunction_bwd := adj.adjunction_bwd
    adjunction_homDim_pairing := hDim }

def AdjointPairData.toWeak
    (adj : AdjointPairData (R := R) (𝔤 := 𝔤)) :
    AdjointPairDataWeak (R := R) (𝔤 := 𝔤) :=
  { F := adj.F
    Fv := adj.Fv
    adjunction_fwd := adj.adjunction_fwd
    adjunction_bwd := adj.adjunction_bwd }

end

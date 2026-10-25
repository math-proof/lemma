/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/Lemma23_4.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.GrothendieckGroupO.Part4
import Lemma.Finset.Zero.le.Form.of.In_PosRoots


noncomputable section

universe u

variable {R : Type u} [CommRing R]
         {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]

def IsDominantCorootNonneg {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) [LinearOrder R] [IsStrictOrderedRing R]
    (lam : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∀ α ∈ rd.posRoots, (0 : R) ≤ rd.corootPairing lam α

end

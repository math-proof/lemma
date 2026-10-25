/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheAmplitudeExchange.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCoordinateBethe.Part6
open Finset


namespace StatMech.FrontierD

noncomputable section

def orderedPairProduct {n : ℕ} {α M : Type*} [CommMonoid M]
    (F : α → α → M) (a : Fin n → α) : M :=
  ∏ k, ∏ l ∈ Finset.Ioi k, F (a k) (a l)

end
end StatMech.FrontierD

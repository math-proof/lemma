/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalExternal.Part3
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalFirstReturn.Part12


namespace StatMech.Onsager

open BigOperators Finset

def ons_decBoundedAtomEmbedding
    {L M N : ℕ} {d : ons_Dart L} (hMN : M ≤ N) :
    ons_DecFirstReturnAtomBounded L d M ↪
      ons_DecFirstReturnAtomBounded L d N :=
  Function.Embedding.sigmaMap (Fin.castLEEmb hMN)
    (fun _ ↦ Function.Embedding.refl _)

end StatMech.Onsager

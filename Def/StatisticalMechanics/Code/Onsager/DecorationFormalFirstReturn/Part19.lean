/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalExternal.Part3
import Abbrev.StatisticalMechanics.Code.Onsager.DecorationFormalFirstReturn.Part4


namespace StatMech.Onsager

open BigOperators Finset

noncomputable def ons_decBoundedRootExponent
    {L N : ℕ} {d : ons_Dart L}
    (root : ons_DecRootedAtomBounded L d N) : ons_DecEdge L →₀ ℕ :=
  ons_decLoopExponent L root.2.1

noncomputable def ons_decBoundedRootWeight
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) {N : ℕ} {d : ons_Dart L}
    (root : ons_DecRootedAtomBounded L d N) : ℂ :=
  ons_decLoopScalar L ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b) root.2.1

def ons_decForgetBoundedRoot
    {L N : ℕ} {d : ons_Dart L} :
    ons_DecRootedAtomBounded L d N ↪ ons_DecRootedAtom L d :=
  Function.Embedding.sigmaMap Fin.valEmbedding
    (fun _ ↦ Function.Embedding.refl _)

end StatMech.Onsager

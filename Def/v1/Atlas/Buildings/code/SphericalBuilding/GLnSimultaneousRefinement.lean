/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnSimultaneousRefinement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.SphericalBuilding.BasisExtensionChain
import Def.v1.Atlas.Buildings.code.SphericalBuilding.AdaptedBasisSingle
import Lemma.Fin.EqLinesFrameOfBasis
import Structure.v1.Atlas.Buildings.code.SphericalBuilding.GLnSimultaneousRefinement
set_option linter.unusedVariables false


namespace GLnBuilding

variable (k : Type*) [Field k] (n : ℕ)

/-- Combining `LatticeChainRefinementHyp` and `FlagToFrameHyp` yields the simultaneous
refinement hypothesis: any finite collection of proper subspaces lies in a common apartment frame. -/
noncomputable def simultaneousRefinementHyp
    (hchain : LatticeChainRefinementHyp k n)
    (hframe : FlagToFrameHyp k n) : SimultaneousRefinementHyp k n where
  refine_list := fun subs hproper => by

    obtain ⟨chain, hcontains, hincr, hlen, hchain_proper⟩ :=
      hchain.refine_via_chain subs hproper

    obtain ⟨F, hF⟩ := hframe.flag_to_frame chain hincr hlen hchain_proper

    exact ⟨F, fun V hV => hF V (hcontains V hV)⟩

end GLnBuilding

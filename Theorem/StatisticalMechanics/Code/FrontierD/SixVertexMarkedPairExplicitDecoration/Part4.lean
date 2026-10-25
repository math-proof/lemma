/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairExplicitDecoration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairExplicitDecoration.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexExplicitMarkedPartialPairing_eq_none_iff
    {T : EvenTorus} {omega eta : SixVertexArrows T} {k : Nat}
    (decoration : SixVertexExplicitMarkedPairDecoration omega eta k)
    (layer : Bool) (v : T.Vertex) :
    sixVertexExplicitMarkedPartialPairing decoration layer v =
        none ↔
      ∃ site ∈ decoration.1.1, site.1 = (layer, v) := by
  dsimp only [sixVertexExplicitMarkedPartialPairing]
  split
  · rename_i hc
    let site : SixVertexPairCTypeSite omega eta :=
      ⟨(layer, v), by
        simpa [sixVertexArrowPairLayer] using hc⟩
    split
    · rename_i hm
      constructor
      · intro h
        exact ⟨site, hm, rfl⟩
      · intro h
        rfl
    · rename_i hm
      constructor
      · intro h
        contradiction
      · rintro ⟨other, hother, hval⟩
        exfalso
        apply hm
        have heq : other = site := Subtype.ext hval
        simpa [heq] using hother
  · rename_i hc
    constructor
    · intro h
      contradiction
    · rintro ⟨site, hsite, hval⟩
      exfalso
      apply hc
      simpa [sixVertexArrowPairLayer, hval] using site.2


end
end StatMech.FrontierD

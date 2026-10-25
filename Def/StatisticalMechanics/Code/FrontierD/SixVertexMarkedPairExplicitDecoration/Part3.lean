/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairExplicitDecoration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall.Part4
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairExplicitDecoration.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexArrowPairLayer
    {T : EvenTorus} (omega eta : SixVertexArrows T) (layer : Bool) :
    SixVertexArrows T :=
  if layer then eta else omega


noncomputable def sixVertexExplicitMarkedPartialPairing
    {T : EvenTorus} {omega eta : SixVertexArrows T} {k : Nat}
    (decoration : SixVertexExplicitMarkedPairDecoration omega eta k)
    (layer : Bool) (v : T.Vertex) : Option Bool :=
  let arrows := sixVertexArrowPairLayer omega eta layer
  if hc : arrows.IsCType v then
    let site : SixVertexPairCTypeSite omega eta :=
      ⟨(layer, v), by simpa [arrows, sixVertexArrowPairLayer] using hc⟩
    if hm : site ∈ decoration.1.1 then none
    else some (decoration.2 ⟨site, hm⟩)
  else some (sixVertexPreferredCompatiblePairing arrows v)

end
end StatMech.FrontierD

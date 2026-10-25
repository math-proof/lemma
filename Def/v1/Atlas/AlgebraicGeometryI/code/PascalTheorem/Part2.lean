/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PascalTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.PascalCurves.Part2
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.PascalCurves
import Structure.v1.Atlas.AlgebraicGeometryI.code.PascalTheorem.Part2
open Polynomial

set_option autoImplicit false


namespace PascalTheoremConics

/-- The cubic associated to an inscribed hexagon: side_A·side_B·side_C - t·opp_A·opp_B·opp_C. -/
noncomputable def InscribedHexagon.cubicP {k : Type*} [Field k] {conic : ProjectiveConic k}
    (hex : InscribedHexagon k conic) : Polynomial k :=
  hex.sideA * hex.sideB * hex.sideC - Polynomial.C hex.t * (hex.oppA * hex.oppB * hex.oppC)

/-- The Pascal line of a hexagon: the quotient of the hexagon cubic by the conic. -/
noncomputable def InscribedHexagon.pascalLine {k : Type*} [Field k]
    {conic : ProjectiveConic k} (hex : InscribedHexagon k conic) : Polynomial k :=
  hex.cubicP /ₘ conic.poly

end PascalTheoremConics

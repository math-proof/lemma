/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PascalTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.PascalCurves.Part2
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.PascalCurves
import Def.v1.Atlas.AlgebraicGeometryI.code.PascalTheorem
open Polynomial

set_option autoImplicit false


namespace PascalTheoremConics

/-- A projective conic given by an irreducible monic polynomial of degree 2. -/
structure ProjectiveConic (k : Type*) [Field k] where
  poly : Polynomial k
  irred : Irreducible poly
  monic : poly.Monic
  deg : poly.natDegree = 2

/-- An inscribed hexagon in a conic: three "sides" and three "opposite sides", each a
polynomial of degree ≤ 1, together with a scalar t making the cubic difference
non-coprime to the conic. -/
structure InscribedHexagon (k : Type*) [Field k] (conic : ProjectiveConic k) where
  sideA : Polynomial k
  sideB : Polynomial k
  sideC : Polynomial k
  oppA : Polynomial k
  oppB : Polynomial k
  oppC : Polynomial k
  sideA_deg : sideA.natDegree ≤ 1
  sideB_deg : sideB.natDegree ≤ 1
  sideC_deg : sideC.natDegree ≤ 1
  oppA_deg : oppA.natDegree ≤ 1
  oppB_deg : oppB.natDegree ≤ 1
  oppC_deg : oppC.natDegree ≤ 1
  t : k
  not_coprime : ¬ IsCoprime conic.poly
    (sideA * sideB * sideC - Polynomial.C t * (oppA * oppB * oppC))

end PascalTheoremConics

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityCurves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalSheafCurves.Part2
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalSheafCurves
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.SheafCohCurvesFiniteness
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.SerreDualityLinear
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.ResidueSum
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.DedekindCurve
import Instance.v1.Atlas.AlgebraicGeometryI.code.SheafCohCurvesFiniteness
import Def.v1.Atlas.AlgebraicGeometryI.code.SerreDualityLinear.Part4
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.SerreDualityGeneral
import Def.v1.Atlas.AlgebraicGeometryI.code.ResidueSum
import Def.v1.Atlas.AlgebraicGeometryI.code.DedekindCurve
import Structure.v1.Atlas.AlgebraicGeometryI.code.SerreDualityCurves


noncomputable section

namespace SerreDualityCurves

open CanonicalSheafCurves RiemannRochCurves SerreDualityP1

open SheafCohCurvesFiniteness CohomologyP1 SheafCohomology


section ResidueMap

variable (k : Type*) [Field k]

/-- The K-theory class of a locally free sheaf is the pair `(rank, degree) ∈ ℤ × ℤ`. -/
def LocallyFreeSheaf.K0class {C : SmoothCompleteCurve}
    (E : LocallyFreeSheaf C) : ℤ × ℤ := (↑E.rk, E.deg)

/-- The Euler characteristic `χ(E) = h⁰(E) - h¹(E)` of a locally free sheaf,
computed from its rank and degree via Riemann–Roch. -/
def LocallyFreeSheaf.chi {C : SmoothCompleteCurve}
    (E : LocallyFreeSheaf C) : ℤ := C.χ E.K0class

/-- The Serre dual `E∨ ⊗ K` at the level of `(rank, degree)`: same rank,
degree replaced by `rank · deg K − deg E`. -/
def LocallyFreeSheaf.serreDual {C : SmoothCompleteCurve}
    (E : LocallyFreeSheaf C) : LocallyFreeSheaf C where
  rk := E.rk
  deg := ↑E.rk * C.degK - E.deg

/-- The line bundle of a given degree. -/
def LocallyFreeSheaf.ofIdeal (C : SmoothCompleteCurve) (deg : ℤ) :
    LocallyFreeSheaf C where
  rk := 1
  deg := deg

/-- The structure sheaf `O_C` as a locally free sheaf of rank `1` and degree `0`. -/
def LocallyFreeSheaf.structureSheaf (C : SmoothCompleteCurve) :
    LocallyFreeSheaf C where
  rk := 1
  deg := 0

/-- The canonical bundle `K_C` as a locally free sheaf of rank `1` and degree `deg K`. -/
def LocallyFreeSheaf.canonical (C : SmoothCompleteCurve) :
    LocallyFreeSheaf C where
  rk := 1
  deg := C.degK

/-- Standalone alias for the structure sheaf of `C`. -/
def structureSheaf (C : SmoothCompleteCurve) : LocallyFreeSheaf C where
  rk := 1
  deg := 0

/-- Standalone alias for the canonical sheaf of `C`. -/
def canonicalSheaf (C : SmoothCompleteCurve) : LocallyFreeSheaf C where
  rk := 1
  deg := C.degK

/-- The projective line `ℙ¹` as a smooth complete curve of genus `0`. -/
def P1Curve : SmoothCompleteCurve := mkCurve 0

/-- The line bundle `O_{ℙ¹}(n)` on `ℙ¹` as a numerical locally free sheaf. -/
def O_P1 (n : ℤ) : LocallyFreeSheaf P1Curve where
  rk := 1
  deg := n

end ResidueMap
end SerreDualityCurves
end

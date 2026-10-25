/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec24RiemannRochSerre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Int.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.GroupTheory.QuotientGroup.Basic
import Structure.v1.Atlas.AlgebraicGeometryI.code.SerreDualityStatement
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.SerreDualityStatement
import Def.v1.Atlas.AlgebraicGeometryI.code.Lec24RiemannRochSerre.Part2
set_option maxHeartbeats 800000


noncomputable section

namespace Lec24

/-- Cohomological consequence of Grothendieck-Birkhoff: every locally free sheaf on `ℙ¹`
matches the cohomology data of a unique split bundle with the right rank and degree. -/
structure LocallyFreeSheafData where
  rk : ℕ
  deg : ℤ
  h0 : ℕ
  h1 : ℕ

/-- Axiomatic data of a smooth complete curve together with a category of coherent sheaves,
their Serre duals, the structure sheaf, the canonical sheaf and the numerical Riemann-Roch
and Serre duality relations they satisfy. -/
structure SmoothCompleteCurveWithSheaves where
  genus : ℕ
  degK : ℤ
  Sheaf : Type
  data : Sheaf → LocallyFreeSheafData
  serreDual : Sheaf → Sheaf
  structureSheaf : Sheaf
  canonicalSheaf : Sheaf

  structureSheaf_rk : (data structureSheaf).rk = 1
  structureSheaf_deg : (data structureSheaf).deg = 0
  structureSheaf_h0 : (data structureSheaf).h0 = 1
  structureSheaf_h1 : (data structureSheaf).h1 = genus

  canonicalSheaf_rk : (data canonicalSheaf).rk = 1
  canonicalSheaf_deg : (data canonicalSheaf).deg = degK

  serreDual_rk : ∀ E, (data (serreDual E)).rk = (data E).rk
  serreDual_deg : ∀ E,
    (data (serreDual E)).deg = (data E).rk * degK - (data E).deg
  serreDual_structure : data (serreDual structureSheaf) = data canonicalSheaf
  serreDual_canonical : data (serreDual canonicalSheaf) = data structureSheaf
  serreDual_involutive : ∀ E, data (serreDual (serreDual E)) = data E
  chi_determined_by_rk_deg : ∀ E : Sheaf,
    ((data E).h0 : ℤ) - ((data E).h1 : ℤ) =
    ↑(data E).rk * (↑(data structureSheaf).h0 - ↑(data structureSheaf).h1) +
    (data E).deg

  serre_duality : ∀ E : Sheaf,
    (data E).h0 = (data (serreDual E)).h1

end Lec24
end

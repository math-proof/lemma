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
import Def.v1.Atlas.AlgebraicGeometryI.code.Lec24RiemannRochSerre.Part4
set_option maxHeartbeats 800000


noncomputable section

namespace Lec24

namespace SmoothCompleteCurveWithSheaves

variable (X : SmoothCompleteCurveWithSheaves)

/-- The Grothendieck group `K_0(Coh X)`: the free abelian group on coherent sheaves modulo
the short-exact-sequence relations. -/
abbrev K0Coh (X : SmoothCurveK0Data) : Type :=
  FreeAbelianGroup X.CohSheaf ⧸ sesRelations X

end SmoothCompleteCurveWithSheaves
end Lec24
end

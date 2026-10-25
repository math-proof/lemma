/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ResidueSumZero.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.ResidueSum
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.ResidueSum
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Over
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Kaehler.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.ResidueSumZero


noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial Finset BigOperators HahnSeries Classical
  IsDedekindDomain

universe u

variable {k : Type u} [Field k]

namespace ResidueSumZero

/-- Additivity of the residue. -/
lemma laurentResidue_add (f g : LaurentSeries k) :
    laurentResidue (f + g) = laurentResidue f + laurentResidue g := by
  simp [laurentResidue, HahnSeries.coeff_add]

/-- The residue is `k`-linear in the scalar action. -/
lemma laurentResidue_smul (c : k) (f : LaurentSeries k) :
    laurentResidue (c • f) = c * laurentResidue f := by
  simp [laurentResidue, HahnSeries.coeff_smul, smul_eq_mul]

end ResidueSumZero
end

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
import Structure.v1.Atlas.AlgebraicGeometryI.code.ResidueSumZero


noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial Finset BigOperators HahnSeries Classical
  IsDedekindDomain

universe u

variable {k : Type u} [Field k]

namespace ResidueSumZero

/-- The local Laurent expansion of `ω` at its `j`-th pole: a pure simple pole
with coefficient `c_j`. -/
noncomputable def PartialFracDiff.localExpansionAtPole
    (ω : PartialFracDiff k) (j : Fin ω.n) : LaurentSeries k :=
  simplePole (ω.c j)

/-- The local Laurent expansion at infinity: a simple pole with residue equal
to `−Σ c_i`, enforcing the residue theorem on `ℙ¹`. -/
noncomputable def PartialFracDiff.localExpansionAtInf
    (ω : PartialFracDiff k) : LaurentSeries k :=
  simplePole (-(∑ i, ω.c i))


end ResidueSumZero
end

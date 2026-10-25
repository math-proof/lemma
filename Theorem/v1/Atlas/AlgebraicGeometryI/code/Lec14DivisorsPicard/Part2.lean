/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec14DivisorsPicard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.CartierDivisorScheme.Part3
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CartierDivisorScheme
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CartierDivisorGroup
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.LocallyFactorialDivisors
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.DivisorsPicard
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.WeilDivisor
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.PicardGroup
import Def.v1.Atlas.AlgebraicGeometryI.code.CartierDivisorGroup.Part2
import Def.v1.Atlas.AlgebraicGeometryI.code.LocallyFactorialDivisors.Part7
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.DivisorsPicard.Part3
import Theorem.v1.Atlas.AlgebraicGeometryI.code.WeilDivisor
import Instance.v1.Atlas.AlgebraicGeometryI.code.PicardGroup
import Theorem.v1.Atlas.AlgebraicGeometryI.code.CohomologyPicard
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.Lec14DivisorsPicard.Part2
open AlgebraicGeometry CategoryTheory


noncomputable section

universe u

namespace Lec14DivisorsPicard

section DedekindCartier

open scoped nonZeroDivisors

variable (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]

variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]

example : CommGroup (cartierDivisorGroupAlg A K) := inferInstance

end DedekindCartier

section WeilCartierGeneral

open LocallyFactorialDivisors

variable (R : Type*) [CommRing R] [IsDomain R]

variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

end WeilCartierGeneral

section WeilCartierDedekind

open scoped nonZeroDivisors

open IsDedekindDomain

variable (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]

variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]

end WeilCartierDedekind

section PicardGroup

open scoped nonZeroDivisors

variable (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]

variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]

end PicardGroup

section LineBundlesCartier

open InvertibleSheaves

variable (R : Type u) [CommRing R]

example : CommGroup (CommRing.Pic R) := inferInstance

end LineBundlesCartier
end Lec14DivisorsPicard
end

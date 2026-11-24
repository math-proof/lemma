module
public import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalSheafCurves.Part2
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalSheafCurves
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.DedekindCurve
public import Def.v1.Atlas.AlgebraicGeometryI.code.DedekindCurve
open CanonicalSheafCurves


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalDivisorCurves.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

namespace CanonicalDivisorCurves

/-- Canonical divisor class of a Dedekind curve `C`: the class of its canonical sheaf in the
Picard-group representation `ℤ × ℤ` (rank, degree). -/
def canonicalDivisorClass_dedekind {k : Type*} [Field k]
    (C : DedekindCurve k) : ℤ × ℤ :=
  canonicalSheafClass C.toSmoothCompleteCurve

end CanonicalDivisorCurves
end

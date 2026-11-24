module
public import Def.v1.Atlas.AlgebraicGeometryI.code.CoherentSheavesCurves.Part2
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.CoherentSheavesCurves
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalBundleProjective
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalBundleGeneral
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannRochCurves
public import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalBundleProjective.Part4
public import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalBundleGeneral
public import Theorem.v1.Atlas.AlgebraicGeometryI.code.RiemannRochCurves
set_option maxHeartbeats 800000
open RiemannRochCurves


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalSheafCurves.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

namespace CanonicalSheafCurves

/-- Existence witness for a smooth complete curve of genus `g`: a Dedekind `k`-algebra `A` whose
Kähler differential module has rank `g`. -/
def CurveWitness (g : ℤ) : Prop :=
  ∃ (k : Type) (_ : Field k) (A : Type) (_ : CommRing A) (_ : IsDomain A)
    (_ : IsDedekindDomain A) (_ : Algebra k A) (_ : Module.Finite k A),
    (Module.finrank k (Ω[A⁄k]) : ℤ) = g

end CanonicalSheafCurves
end

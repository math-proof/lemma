/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/WeilDivisor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.FreeAbelianGroup.Finsupp
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Abbrev.v1.Atlas.AlgebraicGeometryI.code.WeilDivisor.Part2

public section

noncomputable section

namespace WeilDivisor

example (Y : Type*) : AddCommGroup (WeilDivisor.Group Y) := inferInstance


example (R : Type*) [CommRing R] : AddCommGroup (WeilDivisor.DedekindGroup R) := inferInstance

end WeilDivisor
end

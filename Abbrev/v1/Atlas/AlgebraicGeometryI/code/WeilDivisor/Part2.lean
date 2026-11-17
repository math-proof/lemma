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
public import Def.v1.Atlas.AlgebraicGeometryI.code.WeilDivisor


@[expose] public noncomputable section

namespace WeilDivisor

/-- For a Dedekind domain, the Weil divisor group is the free abelian group on
the height-one primes. -/
abbrev DedekindGroup (R : Type*) [CommRing R] :=
  WeilDivisor.Group (IsDedekindDomain.HeightOneSpectrum R)


end WeilDivisor
end

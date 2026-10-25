/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/WeilDivisor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.FreeAbelianGroup.Finsupp
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Def.v1.Atlas.AlgebraicGeometryI.code.WeilDivisor


noncomputable section

namespace WeilDivisor

/-- For a Dedekind domain, the Weil divisor group is the free abelian group on
the height-one primes. -/
abbrev DedekindGroup (R : Type*) [CommRing R] :=
  WeilDivisor.Group (IsDedekindDomain.HeightOneSpectrum R)


end WeilDivisor
end

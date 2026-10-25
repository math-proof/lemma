/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/WeilDivisor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.FreeAbelianGroup.Finsupp
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas


noncomputable section

namespace WeilDivisor

/-- Group of Weil divisors on a "set of codim-1 subvarieties" `Y` (Def 29,
Lec 14): the free abelian group on `Y`, modelled as finitely supported
`ℤ`-valued functions. -/
abbrev Group (Y : Type*) := Y →₀ ℤ


end WeilDivisor
end

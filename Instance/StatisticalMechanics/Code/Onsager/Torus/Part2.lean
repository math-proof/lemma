/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/Torus.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.StatisticalMechanics.Code.Onsager.Torus.Part2


namespace StatMech.Onsager

instance instNeZeroOfFact (L : ℕ) [Fact (2 < L)] : NeZero L :=
  ⟨by have := (Fact.out : 2 < L); omega⟩

instance (L : ℕ) [Fact (2 < L)] : DecidableRel (onsTorusGraph L).Adj :=
  inferInstanceAs (DecidableRel (onsTorusAdj L))

end StatMech.Onsager

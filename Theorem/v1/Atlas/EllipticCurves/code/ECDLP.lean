/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ECDLP.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.EllipticCurves.code.ECDLP.Part2


section Example_9_1

variable [Module (ZMod N) G]

/-- The largest prime factor divides `N`. -/
lemma largestPrimeFactor_dvd (N : ℕ) (hN : 1 < N) :
    largestPrimeFactor N hN ∣ N := by
  have h := Finset.max'_mem _ (Nat.nonempty_primeFactors.mpr hN)
  exact (Nat.mem_primeFactors.mp h).2.1

end Example_9_1

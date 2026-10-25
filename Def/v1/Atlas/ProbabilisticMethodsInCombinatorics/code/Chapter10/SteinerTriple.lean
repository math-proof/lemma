/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/SteinerTriple.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Instance.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter10.SteinerTriple
open MeasureTheory Filter Topology Real Set


noncomputable section

/-- The number of Steiner triple systems on $\{0,\dots,n-1\}$, denoted $\mathrm{STS}(n)$. -/
noncomputable def numSTS (n : ℕ) : ℕ :=
  Nat.card (SteinerTripleSystem (Fin n))

end

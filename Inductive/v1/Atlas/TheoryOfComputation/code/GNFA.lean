/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/GNFA.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Computability.RegularExpressions
import Structure.v1.Atlas.TheoryOfComputation.code.GNFA
open List Set


namespace Sipser

namespace GNFA

variable {Q : Type*} {σ : Type*} [Fintype Q]

/--
`AcceptPath G q q' w` says that the word `w` labels a path in the GNFA `G`
from state `q` to state `q'`: either `w = []` and the path is the trivial
self-loop at `q` (`nil`), or `w = w₁ ++ w₂` where some prefix `w₁` reaches
an intermediate state `qmid` and `w₂` is matched by the regex `G.δ qmid q'`
labelling the edge from `qmid` to `q'` (`cons`).
-/
inductive AcceptPath (G : GNFA Q σ) : Q → Q → List σ → Prop where
  | nil (q : Q) : AcceptPath G q q []
  | cons {q qmid q' : Q} {w₁ w₂ : List σ}
    (path : AcceptPath G q qmid w₁)
    (hmatch : w₂ ∈ (G.δ qmid q').matches') :
    AcceptPath G q q' (w₁ ++ w₂)

end GNFA
end Sipser

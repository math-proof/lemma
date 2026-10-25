/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/GNFA.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Computability.RegularExpressions
import Inductive.v1.Atlas.TheoryOfComputation.code.GNFA
open List Set


namespace Sipser

namespace GNFA

variable {Q : Type*} {σ : Type*} [Fintype Q]

/-- The GNFA `G` *accepts* the word `w` iff there is an `AcceptPath` from
`G.start` to `G.accept` labelled by `w`. -/
def accepts (G : GNFA Q σ) (w : List σ) : Prop :=
  AcceptPath G G.start G.accept w

/-- The language `L(G)` recognised by the GNFA `G`: the set of all words it
accepts. -/
def language (G : GNFA Q σ) : Language σ :=
  { w | G.accepts w }

end GNFA
end Sipser

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/GNFA.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Computability.RegularExpressions
public import Def.v1.Atlas.TheoryOfComputation.code.GNFA
open List Set

public section

namespace Sipser

namespace GNFA

variable {Q : Type*} {σ : Type*} [Fintype Q]

/-- Membership in `G.language` unfolds to `G.accepts`; a `simp` rewrite for
convenience. -/
@[simp] theorem mem_language {G : GNFA Q σ} {w : List σ} :
    w ∈ G.language ↔ G.accepts w :=
  Iff.rfl

end GNFA
end Sipser

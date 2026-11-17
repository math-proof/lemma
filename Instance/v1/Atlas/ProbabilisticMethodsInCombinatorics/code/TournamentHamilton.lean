/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/TournamentHamilton.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.TournamentHamilton

@[expose] public section

namespace TournamentHamilton

variable {n : ℕ}

/-- Decidability of being a Hamilton path. -/
instance (T : Tournament (Fin n)) : DecidablePred T.IsHamiltonPath := by
  intro σ; unfold Tournament.IsHamiltonPath; exact inferInstance

/-- Decidability of being a Hamilton cycle. -/
instance (T : Tournament (Fin n)) : DecidablePred T.IsHamiltonCycle := by
  intro σ; unfold Tournament.IsHamiltonCycle; exact inferInstance

end TournamentHamilton

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Tableau.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TheoryOfComputation.code.Complexity.Part2
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Complexity


namespace TuringMachine

open TuringMachine

/--
A **cell symbol** that may appear in a single cell of a Cook-Levin tableau:
either a tape symbol `γ ∈ Γ` (representing tape contents) or a state `q ∈ Q`
(marking the head position together with the current state).
-/
abbrev CellSymbol (Q : Type) (Γ : Type) := Q ⊕ Γ

end TuringMachine

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Tableau.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TheoryOfComputation.code.Complexity.Part2
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Complexity
import Def.v1.Atlas.TheoryOfComputation.code.Tableau


namespace TuringMachine

open TuringMachine

variable {Q : Type} {Γ : Type} [DecidableEq Q]

/-- Alternative name for `IsLegalWindow`: a legal 6-tuple `(a, b, c, d, e, f)` describing a 2×3 window. -/
abbrev IsLegalSextuple := @IsLegalWindow

end TuringMachine

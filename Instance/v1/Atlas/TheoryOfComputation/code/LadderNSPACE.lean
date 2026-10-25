/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/LadderNSPACE.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TheoryOfComputation.code.SpaceComplexity.Part7
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.SpaceComplexity
import Inductive.v1.Atlas.TheoryOfComputation.code.LadderNSPACE
open Computability TuringMachine SpaceComplexity


namespace SpaceComplexity

/-- The default tape symbol is `blank`. -/
instance {α : Type} : Inhabited (LadderTapeSymbol α) := ⟨LadderTapeSymbol.blank⟩

end SpaceComplexity

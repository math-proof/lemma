/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Reductions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.TheoryOfComputation.code.TuringMachines.Part4
public import Def.v1.Atlas.TheoryOfComputation.code.Reductions

public section


namespace TuringMachine

open TuringMachine

variable {Γ : Type}

/-- Notation `A ≤ₘ B` for mapping reducibility. -/
scoped infixl:50 " ≤ₘ " => MappingReducible

end TuringMachine

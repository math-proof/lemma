/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SelfReference.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Notation.v1.Atlas.TheoryOfComputation.code.Reductions
import Def.v1.Atlas.TheoryOfComputation.code.Decidability.Part13
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Decidability
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Set
import Structure.v1.Atlas.TheoryOfComputation.code.SelfReference.Part3


namespace SelfReference

open TuringMachine

variable {Γ : Type}

/-- The computable map `q(w) := ⟨P_w⟩` inside a `SelfRefFramework`: it sends a
string `w` to the code of the printer-machine that outputs `w`. -/
def SelfRefFramework.q (F : SelfRefFramework Γ) (w : List Γ) : List Γ :=
  F.encode (F.printTM w)

end SelfReference

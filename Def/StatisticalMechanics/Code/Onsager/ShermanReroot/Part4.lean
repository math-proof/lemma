/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanReroot.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.ShermanLemma4.Part3
import Theorem.StatisticalMechanics.Code.Onsager.ShermanSplit.Part5
import Theorem.StatisticalMechanics.Code.Onsager.ShermanReroot.Part3


namespace StatMech.Onsager

open Matrix BigOperators Finset

variable {E : Type*} [Fintype E] [DecidableEq E]

variable {n : ℕ} [NeZero n]


noncomputable def ons_rerootTerm (Lambda : Matrix E E ℂ) (e r : E)
    (v : Fin n → E) : ℂ :=
  if (∀ j, v j ≠ r) ∧ v 0 = e then
    ons_loopWeight Lambda v / (ons_visitCount e v : ℂ)
  else 0

noncomputable def ons_markedTerm (Lambda : Matrix E E ℂ) (e r : E)
    (k : Fin n) (v : Fin n → E) : ℂ :=
  if (∀ j, v j ≠ r) ∧ v k = e then
    ons_loopWeight Lambda v / (ons_visitCount e v : ℂ)
  else 0

end StatMech.Onsager

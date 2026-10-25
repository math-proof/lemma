/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/StateWeightedDeletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationMiddleCancellation


namespace StatMech.Onsager

open Matrix BigOperators

noncomputable def ons_matrixBucketE
    {E : Type*} [Fintype E] [DecidableEq E]
    (M : Matrix E E ℂ) (e r : E) (n : ℕ) : ℂ :=
  ∑ loop ∈ Finset.univ.filter
      (fun loop : Fin (n + 1) → E ↦
        (∃ i, loop i = e) ∧ ¬ ∃ j, loop j = r),
    ons_loopWeight M loop

noncomputable def ons_matrixBucketN
    {E : Type*} [Fintype E] [DecidableEq E]
    (M : Matrix E E ℂ) (e r : E) (n : ℕ) : ℂ :=
  ∑ loop ∈ Finset.univ.filter
      (fun loop : Fin (n + 1) → E ↦
        ¬ (∃ i, loop i = e) ∧ ¬ ∃ j, loop j = r),
    ons_loopWeight M loop

end StatMech.Onsager

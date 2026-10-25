/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexPerScaleBijClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexW2Weight.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexSurgerySeams.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3


namespace StatMech.Universality

open scoped BigOperators

open Filter Topology


open Classical in


noncomputable def hpb_splitEquiv (P Q : List ℤ → Prop) (hsub : ∀ ts, Q ts → P ts) :
    {ts // P ts} ≃ {ts // Q ts} ⊕ {ts // P ts ∧ ¬ Q ts} where
  toFun := fun x => if h : Q x.1 then Sum.inl ⟨x.1, h⟩ else Sum.inr ⟨x.1, x.2, h⟩
  invFun := fun s => s.elim (fun q => ⟨q.1, hsub q.1 q.2⟩) (fun r => ⟨r.1, r.2.1⟩)
  left_inv := by rintro ⟨n, hn⟩; by_cases h : Q n <;> simp [h]
  right_inv := by
    rintro (⟨n, hn⟩ | ⟨n, hn1, hn2⟩)
    · simp [hn]
    · simp [hn2]


end StatMech.Universality

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Max


namespace StatMech.FrontierA

theorem card_subtype_le_iff_card_leftOnly_le_card_rightOnly
    {A : Type*} [Fintype A] (P Q : A -> Prop)
    [DecidablePred P] [DecidablePred Q] :
    Fintype.card {a : A // P a} <= Fintype.card {a : A // Q a} ↔
      Fintype.card {a : A // P a ∧ ¬ Q a} <=
        Fintype.card {a : A // ¬ P a ∧ Q a} := by
  classical
  rw [Fintype.card_subtype, Fintype.card_subtype,
    Fintype.card_subtype, Fintype.card_subtype]
  let s := Finset.univ.filter P
  let t := Finset.univ.filter Q
  have hleft :
      Finset.univ.filter (fun a => P a ∧ ¬ Q a) = s \ t := by
    ext a
    simp [s, t]
  have hright :
      Finset.univ.filter (fun a => ¬ P a ∧ Q a) = t \ s := by
    ext a
    simp [s, t, and_comm]
  rw [hleft, hright]
  change s.card <= t.card ↔ (s \ t).card <= (t \ s).card
  have hs := Finset.card_sdiff_add_card s t
  have ht := Finset.card_sdiff_add_card t s
  rw [Finset.union_comm t s] at ht
  omega


theorem card_subtype_le_of_discrepancyEmbedding
    {A : Type*} [Fintype A] (P Q : A -> Prop)
    [DecidablePred P] [DecidablePred Q]
    (f : {a : A // P a ∧ ¬ Q a} ↪ {a : A // ¬ P a ∧ Q a}) :
    Fintype.card {a : A // P a} <= Fintype.card {a : A // Q a} := by
  rw [card_subtype_le_iff_card_leftOnly_le_card_rightOnly P Q]
  exact Fintype.card_le_of_injective f f.injective


end StatMech.FrontierA

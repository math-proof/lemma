/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyClose.Part5
import Def.StatisticalMechanics.Code.Inequalities.ReimerButterflyProve
open Finset
open scoped FinsetFamily


namespace StatMech

variable {α : Type*} [DecidableEq α]

section Weighted

variable [Fintype α]


theorem wdpairs_symm_eq_wboxValue {w : α → Bool → ℝ} (hsym : ∀ x, w x false = w x true)
    (𝒜 ℬ : Finset (Finset α)) :
    wdpairs w 𝒜 ℬ = wboxValue w (boxDoubled 𝒜 ℬ) := by
  rw [wdpairs_symm_eq_const_mul_count hsym, wboxValue, card_boxDoubled_eq_dpairsCount]


theorem wboxValue_doubleCompress_invariant (w : α → Bool → ℝ) (i : α)
    (𝒰 : Finset (Finset (α ⊕ α))) :
    wboxValue w (doubleCompress i 𝒰) = wboxValue w 𝒰 := by
  unfold wboxValue
  rw [doubleCompress_card]


theorem wdpairs_symm_compress_invariant {w : α → Bool → ℝ} (hsym : ∀ x, w x false = w x true)
    (i : α) (𝒜 ℬ : Finset (Finset α)) :
    wboxValue w (doubleCompress i (boxDoubled 𝒜 ℬ)) = wdpairs w 𝒜 ℬ := by
  rw [wboxValue_doubleCompress_invariant, ← wdpairs_symm_eq_wboxValue hsym]


section RefutationFixedConstant


theorem wdpairs_not_le_wboxValue_general :
    ∃ (w : Fin 1 → Bool → ℝ),
      (∀ x b, 0 ≤ w x b) ∧
      ¬ (wdpairs w ({∅} : Finset (Finset (Fin 1))) {∅}
          ≤ wboxValue w (boxDoubled ({∅} : Finset (Finset (Fin 1))) {∅})) := by
  refine ⟨fun _ b => if b then 1 else 2, fun _ b => by cases b <;> norm_num, ?_⟩
  
  have hwd : wdpairs (fun _ b => if b then (1 : ℝ) else 2) ({∅} : Finset (Finset (Fin 1))) {∅}
      = 4 := by
    unfold wdpairs fwt
    norm_num [Finset.filter_singleton, Finset.disjoint_empty_left]
  
  have hbox : (boxDoubled ({∅} : Finset (Finset (Fin 1))) {∅}).card = 1 := by
    rw [card_boxDoubled_eq_dpairsCount]
    unfold dpairsCount
    norm_num [Finset.filter_singleton, Finset.disjoint_empty_left]
  have hwb : wboxValue (fun _ b => if b then (1 : ℝ) else 2)
      (boxDoubled ({∅} : Finset (Finset (Fin 1))) {∅}) = 1 := by
    unfold wboxValue
    rw [hbox]
    norm_num
  rw [hwd, hwb]; norm_num

end RefutationFixedConstant
end Weighted
end StatMech

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompressionClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerEndpointProve.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyProve.Part2
import Def.StatisticalMechanics.Code.Inequalities.ReimerCompressionClose
open Finset
open scoped FinsetFamily


namespace StatMech

variable {α : Type*} [Fintype α] [DecidableEq α]


variable {β : Type*} [Fintype β] [DecidableEq β]


omit [Fintype β] in
@[simp] lemma iterDoubleCompress_nil (𝒰 : Finset (Finset (β ⊕ β))) :
    iterDoubleCompress [] 𝒰 = 𝒰 := rfl

omit [Fintype β] in
@[simp] lemma iterDoubleCompress_cons (i : β) (is : List β) (𝒰 : Finset (Finset (β ⊕ β))) :
    iterDoubleCompress (i :: is) 𝒰 = doubleCompress i (iterDoubleCompress is 𝒰) := rfl

omit [Fintype β] in


theorem iterDoubleCompress_card (is : List β) (𝒰 : Finset (Finset (β ⊕ β))) :
    (iterDoubleCompress is 𝒰).card = 𝒰.card := by
  induction is with
  | nil => rfl
  | cons i is ih => rw [iterDoubleCompress_cons, doubleCompress_card, ih]


theorem fmarg_le_iterDoubleCompress {w : (β ⊕ β) → Bool → ℝ} (hw0 : ∀ x b, 0 ≤ w x b)
    (hL : ∀ i, w (Sum.inl i) true ≤ w (Sum.inl i) false)
    (hR : ∀ i, w (Sum.inr i) false ≤ w (Sum.inr i) true)
    (is : List β) (𝒰 : Finset (Finset (β ⊕ β))) :
    fmarg w 𝒰 ≤ fmarg w (iterDoubleCompress is 𝒰) := by
  induction is with
  | nil => simp
  | cons i is ih =>
      rw [iterDoubleCompress_cons]
      exact ih.trans (fmarg_le_doubleCompress hw0 i (hL i) (hR i) _)


theorem fmarg_le_downCompression_satisfiable (a : α) (𝒜 : Finset (Finset α)) :
    fmarg (fun _ _ => (1 : ℝ)) 𝒜 ≤ fmarg (fun _ _ => (1 : ℝ)) (Down.compression a 𝒜) :=
  fmarg_le_downCompression (fun _ _ => zero_le_one) a (le_refl _) 𝒜


theorem fmarg_le_doubleCompress_symm {w : (β ⊕ β) → Bool → ℝ} (hw0 : ∀ x b, 0 ≤ w x b)
    (hsym : ∀ x, w x false = w x true) (i : β) (𝒰 : Finset (Finset (β ⊕ β))) :
    fmarg w 𝒰 ≤ fmarg w (doubleCompress i 𝒰) :=
  fmarg_le_doubleCompress hw0 i (le_of_eq (hsym _).symm) (le_of_eq (hsym _)) 𝒰


theorem fmarg_doubleCompress_symm_eq {w : (β ⊕ β) → Bool → ℝ}
    (hsym : ∀ x, w x false = w x true) (i : β) (𝒰 : Finset (Finset (β ⊕ β))) :
    fmarg w (doubleCompress i 𝒰) = fmarg w 𝒰 := by
  have hconst : ∀ S : Finset (β ⊕ β), fwt w S = ∏ x, w x true := fwt_symm_eq_const hsym
  calc fmarg w (doubleCompress i 𝒰)
      = (∏ x, w x true) * ((doubleCompress i 𝒰).card : ℝ) := by
        rw [fmarg]; rw [Finset.sum_congr rfl (fun S _ => hconst S), Finset.sum_const,
          nsmul_eq_mul, mul_comm]
    _ = (∏ x, w x true) * (𝒰.card : ℝ) := by rw [doubleCompress_card]
    _ = fmarg w 𝒰 := by
        rw [fmarg]; rw [Finset.sum_congr rfl (fun S _ => hconst S), Finset.sum_const,
          nsmul_eq_mul, mul_comm]


theorem fmarg_boxDoubled_doubleWeight (w : β → Bool → ℝ) (𝒜 ℬ : Finset (Finset β)) :
    fmarg (doubleWeight w) (boxDoubled 𝒜 ℬ) = wdpairs w 𝒜 ℬ :=
  fmarg_boxDoubled w 𝒜 ℬ


theorem wdpairs_le_iterDoubleCompress_of_symm {w : β → Bool → ℝ}
    (hw0 : ∀ x b, 0 ≤ w x b) (hsym : ∀ x, w x false = w x true)
    (is : List β) (𝒜 ℬ : Finset (Finset β)) :
    wdpairs w 𝒜 ℬ
      ≤ fmarg (doubleWeight w) (iterDoubleCompress is (boxDoubled 𝒜 ℬ)) := by
  have hsymD : ∀ x, doubleWeight w x false = doubleWeight w x true := by
    rintro (a | a) <;> simp only [doubleWeight_apply_inl, doubleWeight_apply_inr] <;> exact hsym a
  have hkey := fmarg_le_iterDoubleCompress (doubleWeight_nonneg hw0)
    (fun i => le_of_eq (hsymD (Sum.inl i)).symm)
    (fun i => le_of_eq (hsymD (Sum.inr i))) is (boxDoubled 𝒜 ℬ)
  rwa [fmarg_boxDoubled_doubleWeight] at hkey


theorem wdpairs_le_mul_of_symm {w : β → Bool → ℝ}
    (hw0 : ∀ x b, 0 ≤ w x b) (hw1 : ∀ x, w x false + w x true = 1)
    (𝒜 ℬ : Finset (Finset β)) :
    wdpairs w 𝒜 ℬ ≤ fmarg w 𝒜 * fmarg w ℬ :=
  wdpairs_le_mul_of_doubled_independence hw0 hw1 𝒜 ℬ


end StatMech

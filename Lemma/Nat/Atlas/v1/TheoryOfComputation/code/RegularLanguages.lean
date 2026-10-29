import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.TheoryOfComputation.code.RegularLanguages
open Computability RegularLanguages
open Language Set


namespace RegularLanguages

/--
[regular_union](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/RegularLanguages.lean)
-/
@[path]
lemma regular_union
  {A B : Language α}
-- given
  (hA : IsRegular A)
  (hB : IsRegular B) :
-- imply
  IsRegular (A + B) := by
-- proof

  unfold IsRegular at *

  obtain ⟨σ₁, _, M₁, hM₁⟩ := hA
  obtain ⟨σ₂, _, M₂, hM₂⟩ := hB


  exact ⟨σ₁ × σ₂, inferInstance, M₁.union M₂, by simp [hM₁, hM₂]⟩

end RegularLanguages
namespace RegularLanguages
open Language Set

end RegularLanguages

namespace RegularLanguages

/--
[kstar_append](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/RegularLanguages.lean)
-/
@[path]
lemma kstar_append
  {A : Language α}
  {x y : List α}
-- given
  (hx : x ∈ KStar.kstar A)
  (hy : y ∈ KStar.kstar A) :
-- imply
  x ++ y ∈ KStar.kstar A := by
-- proof
  rw [mem_kstar] at hx hy ⊢
  obtain ⟨L₁, hf₁, hL₁⟩ := hx; obtain ⟨L₂, hf₂, hL₂⟩ := hy
  exact ⟨L₁ ++ L₂, by simp [hf₁, hf₂], fun w hw => by
    simp at hw; rcases hw with h | h <;> [exact hL₁ w h; exact hL₂ w h]⟩

end RegularLanguages

namespace RegularLanguages

/--
[kstar_cons](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/RegularLanguages.lean)
-/
@[path]
lemma kstar_cons
  {A : Language α}
  {w y : List α}
-- given
  (hw : w ∈ A)
  (hy : y ∈ KStar.kstar A) :
-- imply
  w ++ y ∈ KStar.kstar A := by
-- proof
  rw [mem_kstar] at hy ⊢; obtain ⟨L, hf, hL⟩ := hy
  refine ⟨w :: L, by simp [hf], fun v hv => ?_⟩
  rcases List.mem_cons.mp hv with rfl | hv <;> [exact hw; exact hL v hv]

end RegularLanguages

namespace RegularLanguages

/--
[kstar_split](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/RegularLanguages.lean)
-/
@[path]
lemma kstar_split
  {A : Language α}
  {x y : List α}
-- given
  (h : x ++ y ∈ KStar.kstar A) :
-- imply
  (x ∈ KStar.kstar A ∧ y ∈ KStar.kstar A) ∨ (∃ p c d r, p ∈ KStar.kstar A ∧ x = p ++ c ∧ c ≠ [] ∧ c ++ d ∈ A ∧ r ∈ KStar.kstar A ∧ y = d ++ r) := by
-- proof
  rw [mem_kstar] at h; obtain ⟨L, hfl, hL⟩ := h
  induction L generalizing x with
  | nil =>
    simp [List.flatten] at hfl
    have hx : x = [] := by cases x <;> simp_all
    subst hx; simp at hfl; subst hfl
    exact Or.inl ⟨nil_mem_kstar A, nil_mem_kstar A⟩
  | cons w L ih =>
    simp [List.flatten] at hfl
    have hw : w ∈ A := hL w (List.mem_cons.mpr (Or.inl rfl))
    have hL' : ∀ v ∈ L, v ∈ A := fun v hv => hL v (List.mem_cons.mpr (Or.inr hv))
    rcases List.append_eq_append_iff.mp hfl with ⟨c, hc1, hc2⟩ | ⟨c, hc1, hc2⟩
    ·
      by_cases hx : x = []
      ·
        subst hx; simp at hc1; subst hc1
        left; exact ⟨nil_mem_kstar A, hc2 ▸ kstar_cons hw (join_mem_kstar hL')⟩
      ·
        right
        exact ⟨[], x, c, L.flatten, nil_mem_kstar A, by simp, hx,
          hc1 ▸ hw, join_mem_kstar hL', hc2⟩
    ·
      rcases ih hc2.symm hL' with
        ⟨hc_star, hy_star⟩ | ⟨p, c', d, r, hp, hcp, hc', hcd, hr, hyr⟩
      · left; exact ⟨hc1 ▸ kstar_cons hw hc_star, hy_star⟩
      · right; exact ⟨w ++ p, c', d, r, kstar_cons hw hp,
          by rw [hc1, hcp, List.append_assoc], hc', hcd, hr, hyr⟩

end RegularLanguages

namespace RegularLanguages

/--
[kstar_leftQuotient_transfer](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/RegularLanguages.lean)
-/
@[path]
lemma kstar_leftQuotient_transfer
  {A : Language α}
  {x₁ x₂ y : List α}
-- given
  (hS : A.leftQuotient '' { c | ∃ p ∈ KStar.kstar A, x₁ = p ++ c ∧ c ≠ [] } ⊆ A.leftQuotient '' { c | ∃ p ∈ KStar.kstar A, x₂ = p ++ c ∧ c ≠ [] })
  (hB : x₁ ∈ KStar.kstar A → x₂ ∈ KStar.kstar A)
  (hy : x₁ ++ y ∈ KStar.kstar A) :
-- imply
  x₂ ++ y ∈ KStar.kstar A := by
-- proof
  rcases kstar_split hy with
    ⟨hx₁_star, hy_star⟩ | ⟨p, c, d, r, hp, hxpc, hc, hcd, hr, hyr⟩
  ·
    exact kstar_append (hB hx₁_star) hy_star
  ·

    have hmem : A.leftQuotient c ∈
        A.leftQuotient '' { c | ∃ p ∈ KStar.kstar A, x₁ = p ++ c ∧ c ≠ [] } :=
      ⟨c, ⟨p, hp, hxpc, hc⟩, rfl⟩
    obtain ⟨c', ⟨p', hp', hx₂pc', _⟩, heq⟩ := hS hmem


    have hd : d ∈ A.leftQuotient c' := by rw [heq, mem_leftQuotient]; exact hcd
    subst hyr

    rw [hx₂pc', List.append_assoc,
        show c' ++ (d ++ r) = (c' ++ d) ++ r from (List.append_assoc _ _ _).symm]
    exact kstar_append hp' (kstar_cons ((mem_leftQuotient c' d).mp hd) hr)

end RegularLanguages

namespace RegularLanguages

/--
[leftQuotient_kstar_determined](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/RegularLanguages.lean)
-/
@[path]
lemma leftQuotient_kstar_determined
  (A : Language α)
  (x₁ x₂ : List α)
-- given
  (hS : A.leftQuotient '' { c | ∃ p ∈ KStar.kstar A, x₁ = p ++ c ∧ c ≠ [] } = A.leftQuotient '' { c | ∃ p ∈ KStar.kstar A, x₂ = p ++ c ∧ c ≠ [] })
  (hB : (x₁ ∈ KStar.kstar A) = (x₂ ∈ KStar.kstar A)) :
-- imply
  (KStar.kstar A).leftQuotient x₁ = (KStar.kstar A).leftQuotient x₂ := by
-- proof
  ext y; simp only [mem_leftQuotient]
  exact ⟨kstar_leftQuotient_transfer (hS ▸ le_refl _) (hB ▸ id),
         kstar_leftQuotient_transfer (hS.symm ▸ le_refl _) (hB.symm ▸ id)⟩

end RegularLanguages

namespace RegularLanguages

/--
[finite_range_prop](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/RegularLanguages.lean)
-/
@[path]
lemma finite_range_prop
-- given
  (f : X → Prop) :
-- imply
  Set.Finite (Set.range f) := by
-- proof
  apply Set.Finite.subset (Set.Finite.insert True (Set.finite_singleton False))
  intro p ⟨n, hn⟩; subst hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  by_cases h : f n
  · left; exact propext ⟨fun _ => trivial, fun _ => h⟩
  · right; exact propext ⟨fun hf => absurd hf h, False.elim⟩

end RegularLanguages

namespace RegularLanguages

/--
[regular_star](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/RegularLanguages.lean)
-/
@[path]
lemma regular_star
  {A : Language α}
-- given
  (hA : A.IsRegular) :
-- imply
  (KStar.kstar A).IsRegular := by
-- proof
  apply Language.IsRegular.of_finite_range_leftQuotient

  set descr : List α → Set (Language α) × Prop :=
    fun x => (A.leftQuotient '' { c | ∃ p ∈ KStar.kstar A, x = p ++ c ∧ c ≠ [] },
              x ∈ KStar.kstar A) with descr_def

  have hfin_descr : (Set.range descr).Finite := by
    apply Set.Finite.subset
      (Set.Finite.prod hA.finite_range_leftQuotient.powerset (finite_range_prop _))
    rintro ⟨S, b⟩ ⟨x, hx⟩
    simp only [descr_def] at hx
    exact ⟨by rw [Set.mem_powerset_iff, ← (Prod.ext_iff.mp hx).1]
              exact Set.image_subset_range _ _,
           ⟨x, (Prod.ext_iff.mp hx).2⟩⟩

  have hfactor : ∀ x₁ x₂, descr x₁ = descr x₂ →
      (KStar.kstar A).leftQuotient x₁ = (KStar.kstar A).leftQuotient x₂ := by
    intro x₁ x₂ h
    exact leftQuotient_kstar_determined A x₁ x₂
      (Prod.ext_iff.mp h).1 (Prod.ext_iff.mp h).2

  apply Set.Finite.subset
    (hfin_descr.image ((KStar.kstar A).leftQuotient ∘ Function.invFun descr))
  rintro L ⟨x, rfl⟩
  exact ⟨descr x, ⟨x, rfl⟩, hfactor _ _ (Function.invFun_eq ⟨x, rfl⟩)⟩

end RegularLanguages
namespace RegularLanguages
open Computability

end RegularLanguages

namespace RegularLanguages

/--
[DFA.pumping_lemma'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/RegularLanguages.lean)
-/
@[path]
lemma DFA.pumping_lemma'
  {M : DFA α σ}
  [Fintype σ]
  {s : List α}
-- given
  (hs : s ∈ M.accepts)
  (hlen : Fintype.card σ ≤ s.length) :
-- imply
  ∃ x y z, s = x ++ y ++ z ∧ x.length + y.length ≤ Fintype.card σ ∧ y ≠ [] ∧ {x} * {y}∗ * {z} ≤ M.accepts :=
-- proof
  M.pumping_lemma hs hlen

end RegularLanguages

namespace RegularLanguages

/--
[pumping_lemma](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/RegularLanguages.lean)
-/
@[path]
lemma pumping_lemma
  {A : Language α}
-- given
  (hA : IsRegular A) :
-- imply
  ∃ p : ℕ, 0 < p ∧ ∀ s ∈ A, p ≤ s.length → ∃ x y z : List α, s = x ++ y ++ z ∧ x.length + y.length ≤ p ∧ y ≠ [] ∧ {x} * {y}∗ * {z} ≤ A := by
-- proof

  obtain ⟨σ, hfin, M, hM⟩ := hA

  have : Nonempty σ := ⟨M.start⟩
  refine ⟨Fintype.card σ, Fintype.card_pos, ?_⟩

  intro s hs hlen
  rw [← hM] at hs
  obtain ⟨x, y, z, hsplit, hxylen, hne, hpump⟩ := M.pumping_lemma hs hlen
  exact ⟨x, y, z, hsplit, hxylen, hne, hM ▸ hpump⟩

end RegularLanguages
namespace RegularLanguages
open Language Set

end RegularLanguages

namespace RegularLanguages

/--
[leftQuotient_mul_determined](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/RegularLanguages.lean)
-/
@[path]
lemma leftQuotient_mul_determined
  (A B : Language α)
  (x₁ x₂ : List α)
-- given
  (h1 : A.leftQuotient x₁ = A.leftQuotient x₂)
  (h2 : B.leftQuotient '' { c | ∃ a ∈ A, x₁ = a ++ c } = B.leftQuotient '' { c | ∃ a ∈ A, x₂ = a ++ c }) :
-- imply
  (A * B).leftQuotient x₁ = (A * B).leftQuotient x₂ := by
-- proof
  ext y
  simp only [mem_leftQuotient, Language.mem_mul]
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    rcases List.append_eq_append_iff.mp hab with ⟨c, hc1, hc2⟩ | ⟨c, hc1, hc2⟩
    · have hmem : B.leftQuotient c ∈ B.leftQuotient '' { c | ∃ a ∈ A, x₁ = a ++ c } :=
        ⟨c, ⟨a, ha, hc1⟩, rfl⟩
      rw [h2] at hmem
      obtain ⟨c', ⟨a', ha', hc1'⟩, heq⟩ := hmem
      refine ⟨a', ha', c' ++ y, ?_, by rw [hc1', List.append_assoc]⟩
      rw [← mem_leftQuotient, heq, mem_leftQuotient]
      exact hc2 ▸ hb
    · exact ⟨x₂ ++ c,
        by rw [← mem_leftQuotient, ← h1, mem_leftQuotient, ← hc1]; exact ha,
        b, hb, by rw [List.append_assoc, hc2.symm]⟩
  · rintro ⟨a, ha, b, hb, hab⟩
    rcases List.append_eq_append_iff.mp hab with ⟨c, hc1, hc2⟩ | ⟨c, hc1, hc2⟩
    · have hmem : B.leftQuotient c ∈ B.leftQuotient '' { c | ∃ a ∈ A, x₂ = a ++ c } :=
        ⟨c, ⟨a, ha, hc1⟩, rfl⟩
      rw [← h2] at hmem
      obtain ⟨c', ⟨a', ha', hc1'⟩, heq⟩ := hmem
      refine ⟨a', ha', c' ++ y, ?_, by rw [hc1', List.append_assoc]⟩
      rw [← mem_leftQuotient, heq, mem_leftQuotient]
      exact hc2 ▸ hb
    · exact ⟨x₁ ++ c,
        by rw [← mem_leftQuotient, h1, mem_leftQuotient, ← hc1]; exact ha,
        b, hb, by rw [List.append_assoc, hc2.symm]⟩

end RegularLanguages

namespace RegularLanguages

/--
[regular_concat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/RegularLanguages.lean)
-/
@[path]
lemma regular_concat
  {A B : Language α}
-- given
  (hA : A.IsRegular)
  (hB : B.IsRegular) :
-- imply
  (A * B).IsRegular := by
-- proof
  apply Language.IsRegular.of_finite_range_leftQuotient

  set descr : List α → Language α × Set (Language α) :=
    fun x => (A.leftQuotient x, B.leftQuotient '' { c | ∃ a ∈ A, x = a ++ c }) with descr_def


  have hfin_descr : (range descr).Finite := by
    apply Set.Finite.subset
      (Set.Finite.prod hA.finite_range_leftQuotient hB.finite_range_leftQuotient.powerset)
    rintro ⟨L, S⟩ ⟨x, hx⟩
    simp only [descr_def] at hx
    exact ⟨⟨x, (Prod.ext_iff.mp hx).1⟩,
      by rw [mem_powerset_iff, ← (Prod.ext_iff.mp hx).2]; exact image_subset_range _ _⟩

  have hfactor : ∀ x₁ x₂, descr x₁ = descr x₂ →
      (A * B).leftQuotient x₁ = (A * B).leftQuotient x₂ := by
    intro x₁ x₂ h
    exact leftQuotient_mul_determined A B x₁ x₂
      (Prod.ext_iff.mp h).1 (Prod.ext_iff.mp h).2

  apply Set.Finite.subset (hfin_descr.image ((A * B).leftQuotient ∘ Function.invFun descr))
  rintro L ⟨x, rfl⟩
  exact ⟨descr x, ⟨x, rfl⟩, hfactor _ _ (Function.invFun_eq ⟨x, rfl⟩)⟩

end RegularLanguages


-- created on 2026-10-23
-- updated on 2026-10-28

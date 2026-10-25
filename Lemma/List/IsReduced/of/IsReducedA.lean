import Mathlib
import sympy.Basic
import Def.v1.Atlas.Buildings.code.CoxeterGroup.BruhatSubexpression
import Lemma.List.Any_And_Eq_WordProd.of.Eq_WordProd.IsReduced.BruhatLE.ReducedSublistProperty.StrongExchangeCondition


namespace CoxeterBruhat

/--
[isReduced_tail](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/SupportWellDefined.lean)
-/
@[path]
lemma isReduced_tail
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {a : B}
  {rest : List B}
-- given
  (hred : cs.IsReduced (a :: rest)) :
-- imply
  cs.IsReduced rest := by
-- proof
  unfold CoxeterSystem.IsReduced at *
  have hle := cs.length_wordProd_le rest
  rw [cs.wordProd_cons, List.length_cons] at hred
  obtain h | h <;> omega := cs.length_simple_mul (cs.wordProd rest) a

end CoxeterBruhat

namespace CoxeterBruhat

/--
[isReduced_dropLast](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/SupportWellDefined.lean)
-/
@[path]
lemma isReduced_dropLast
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {ω : List B}
-- given
  (hne : ω ≠ [])
  (hred : cs.IsReduced ω) :
-- imply
  cs.IsReduced ω.dropLast := by
-- proof
  unfold CoxeterSystem.IsReduced at *
  have hle := cs.length_wordProd_le ω.dropLast
  rw [List.dropLast_append_getLast hne |>.symm, cs.wordProd_append, cs.wordProd_singleton,
    List.length_append, List.length_singleton] at hred
  obtain h | h <;> omega := cs.length_mul_simple (cs.wordProd ω.dropLast) (ω.getLast hne)

end CoxeterBruhat

namespace CoxeterBruhat

/--
[isReduced_length_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/SupportWellDefined.lean)
-/
@[path]
lemma isReduced_length_eq
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {ω₁ ω₂ : List B}
-- given
  (h0 : cs.IsReduced ω₁)
  (h1 : cs.IsReduced ω₂)
  (heq : cs.wordProd ω₁ = cs.wordProd ω₂) :
-- imply
  ω₁.length = ω₂.length := by
-- proof
  unfold CoxeterSystem.IsReduced at *; rw [heq] at h1; omega

end CoxeterBruhat

namespace CoxeterBruhat

/--
[List.toFinset_sublist_subset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/SupportWellDefined.lean)
-/
@[path]
lemma List.toFinset_sublist_subset
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {l₁ l₂ : List B}
-- given
  (h : l₁.Sublist l₂) :
-- imply
  l₁.toFinset ⊆ l₂.toFinset :=
-- proof
  fun _ hx => List.mem_toFinset.mpr (h.mem (List.mem_toFinset.mp hx))

end CoxeterBruhat

namespace CoxeterBruhat

/--
[toFinset_cover](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/SupportWellDefined.lean)
-/
@[path]
lemma toFinset_cover
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {a b : B}
  {rest : List B} :
-- imply
  (a :: b :: rest).toFinset ⊆ (b :: rest).toFinset ∪ (a :: b :: rest).dropLast.toFinset := by
-- proof
  intro x hx
  simp only [List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, Finset.mem_union] at *
  obtain rfl | hx := hx
  · right
    rw [List.dropLast_cons_of_ne_nil (List.cons_ne_nil b rest)]
    simp [List.mem_cons]
  · left; exact hx

end CoxeterBruhat

namespace CoxeterBruhat

/--
[support_subset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/SupportWellDefined.lean)
-/
@[path]
lemma support_subset
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {ω₁ ω₂ : List B}
-- given
  (hSEC_full : StrongExchangeCondition cs)
  (hRSP : ReducedSublistProperty cs)
  (hSEC : StrongExchangeForBruhat cs)
  (hred₁ : cs.IsReduced ω₁)
  (hred₂ : cs.IsReduced ω₂)
  (heq : cs.wordProd ω₁ = cs.wordProd ω₂) :
-- imply
  ω₁.toFinset ⊆ ω₂.toFinset := by
-- proof
  suffices h : ∀ (n : ℕ) {ω₁ ω₂ : List B},
    cs.IsReduced ω₁ → cs.IsReduced ω₂ →
    cs.wordProd ω₁ = cs.wordProd ω₂ → ω₁.length ≤ n →
    ω₁.toFinset ⊆ ω₂.toFinset from
    h ω₁.length hred₁ hred₂ heq le_rfl
  intro n
  induction n with
  | zero =>
    intro ω₁ ω₂ _ _ _ hlen
    have : ω₁ = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
    subst this; simp
  | succ n ih =>
    intro ω₁ ω₂ hred₁ hred₂ heq hlen
    match ω₁, hred₁, hlen with
    | [], _, _ => simp
    | [a], hred_a, _ =>
      have hlen₂ : ω₂.length = 1 := by
        have := isReduced_length_eq cs [a] ω₂ hred_a hred₂ heq; simp at this; omega
      obtain ⟨b, rfl⟩ : ∃ b, ω₂ = [b] := by
        match ω₂, hlen₂ with
        | [b], _ => exact ⟨b, rfl⟩
      simp only [cs.wordProd_singleton] at heq
      have hab : a = b := CoxeterSystem.simple_injective cs heq
      subst hab; exact Finset.Subset.refl _
    | a :: b :: rest, hred_abr, hlen_abr =>
      have hred_tail : cs.IsReduced (b :: rest) :=
        isReduced_tail cs a (b :: rest) hred_abr
      have hred_drop : cs.IsReduced (a :: b :: rest).dropLast :=
        isReduced_dropLast cs (a :: b :: rest) (List.cons_ne_nil a _) hred_abr
      have htail_lt : (b :: rest).length < (a :: b :: rest).length := by simp
      have hdrop_lt : (a :: b :: rest).dropLast.length < (a :: b :: rest).length := by
        simp [List.length_dropLast]
      have htail_sub : (b :: rest).Sublist (a :: b :: rest) := List.sublist_cons_self a _
      have htail_le : BruhatLE cs (cs.wordProd (b :: rest)) (cs.wordProd (a :: b :: rest)) :=
        subexpression_bruhatLE_backward cs hSEC hred_abr rfl htail_sub rfl
      rw [heq] at htail_le
      obtain ⟨σ, hσ_sub, hσ_eq⟩ :=
        bruhatLE_subexpression_forward cs hSEC_full hRSP htail_le hred₂ rfl
      obtain ⟨τ, hτ_sub_σ, hτ_red, hτ_prod⟩ := hRSP σ
      have hτ_prod' : cs.wordProd (b :: rest) = cs.wordProd τ := by
        rw [hσ_eq, hτ_prod]
      have hτ_len : τ.length = (b :: rest).length :=
        isReduced_length_eq cs τ (b :: rest) hτ_red hred_tail hτ_prod'.symm
      have hτ_le_n : τ.length ≤ n := by simp only [List.length_cons] at *; omega
      have hτ_sub_ω₂ : τ.toFinset ⊆ ω₂.toFinset :=
        List.toFinset_sublist_subset (hτ_sub_σ.trans hσ_sub)
      have htail_sub_τ : (b :: rest).toFinset ⊆ τ.toFinset :=
        ih hred_tail hτ_red hτ_prod' (by simp only [List.length_cons] at *; omega)
      have htail_sub_ω₂ : (b :: rest).toFinset ⊆ ω₂.toFinset :=
        htail_sub_τ.trans hτ_sub_ω₂
      have hdrop_sub : (a :: b :: rest).dropLast.Sublist (a :: b :: rest) :=
        List.dropLast_sublist _
      have hdrop_le : BruhatLE cs (cs.wordProd (a :: b :: rest).dropLast)
        (cs.wordProd (a :: b :: rest)) :=
        subexpression_bruhatLE_backward cs hSEC hred_abr rfl hdrop_sub rfl
      rw [heq] at hdrop_le
      obtain ⟨σ', hσ'_sub, hσ'_eq⟩ :=
        bruhatLE_subexpression_forward cs hSEC_full hRSP hdrop_le hred₂ rfl
      obtain ⟨τ', hτ'_sub_σ', hτ'_red, hτ'_prod⟩ := hRSP σ'
      have hτ'_prod' : cs.wordProd (a :: b :: rest).dropLast = cs.wordProd τ' := by
        rw [hσ'_eq, hτ'_prod]
      have hτ'_sub_ω₂ : τ'.toFinset ⊆ ω₂.toFinset :=
        List.toFinset_sublist_subset (hτ'_sub_σ'.trans hσ'_sub)
      have hdrop_sub_τ' : (a :: b :: rest).dropLast.toFinset ⊆ τ'.toFinset :=
        ih hred_drop hτ'_red hτ'_prod' (by simp only [List.length_cons, List.length_dropLast] at *; omega)
      have hdrop_sub_ω₂ : (a :: b :: rest).dropLast.toFinset ⊆ ω₂.toFinset :=
        hdrop_sub_τ'.trans hτ'_sub_ω₂
      intro x hx
      have hcover := toFinset_cover a b rest hx
      simp only [Finset.mem_union] at hcover
      obtain h | h := hcover
      · exact htail_sub_ω₂ h
      · exact hdrop_sub_ω₂ h

end CoxeterBruhat


-- created on 2026-10-23

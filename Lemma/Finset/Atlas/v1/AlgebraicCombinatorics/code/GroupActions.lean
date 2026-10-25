import Mathlib
import sympy.Basic
import Abbrev.v1.Atlas.AlgebraicCombinatorics.code.GroupActions
open SpernerProperty MulAction Finset GroupActions GraphIsoPoset
open scoped Classical Pointwise
open SpernerProperty GroupActions


namespace GroupActions

/--
[quotientPosetCompl_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/GroupActions.lean)
-/
@[path]
lemma quotientPosetCompl_antitone
  {n : ℕ}
  {G : Subgroup (Equiv.Perm (Fin n))} :
-- imply
  Antitone (quotientPosetCompl (n := n) (G := G)) := by
-- proof
  intro a b hab
  obtain ⟨S, T, rfl, rfl, hST⟩ := hab
  exact ⟨Finset.univ \ T, Finset.univ \ S,
    (quotientPosetCompl_mk T).symm, (quotientPosetCompl_mk S).symm,
    Finset.sdiff_subset_sdiff Subset.rfl hST⟩

end GroupActions

namespace GroupActions

/--
[quotientPosetCompl_strictAnti](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/GroupActions.lean)
-/
@[path]
lemma quotientPosetCompl_strictAnti
  {n : ℕ}
  {G : Subgroup (Equiv.Perm (Fin n))} :
-- imply
  StrictAnti (quotientPosetCompl (n := n) (G := G)) := by
-- proof
  intro a b hab
  obtain ⟨hab_le, hab_ne⟩ := hab
  refine ⟨quotientPosetCompl_antitone hab_le, fun hba => hab_ne ?_⟩
  have h1 := quotientPosetCompl_antitone hba
  rwa [quotientPosetCompl_involutive, quotientPosetCompl_involutive] at h1

end GroupActions

namespace GroupActions

/--
[quotientPosetCompl_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/GroupActions.lean)
-/
@[path]
lemma quotientPosetCompl_injective
  {n : ℕ}
  {G : Subgroup (Equiv.Perm (Fin n))} :
-- imply
  Function.Injective (quotientPosetCompl (n := n) (G := G)) :=
-- proof
  quotientPosetCompl_involutive.injective

end GroupActions

namespace GroupActions

/--
[quotientPosetCompl_grade'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/GroupActions.lean)
-/
@[path]
lemma quotientPosetCompl_grade'
  {n : ℕ}
  {G : Subgroup (Equiv.Perm (Fin n))}
  {q : QuotientPoset n G} :
-- imply
  letI := quotientPoset_gradeMinOrder n G grade ℕ (quotientPosetCompl q) = n - grade ℕ q :=
-- proof
  quotientPosetRank_compl q

end GroupActions

namespace GroupActions

/--
[embedOrbits_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/GroupActions.lean)
-/
@[path]
lemma embedOrbits_injective
  {n : ℕ}
  {G : Subgroup (Equiv.Perm (Fin n))}
  {i : ℕ} :
-- imply
  Function.Injective (embedOrbits (n := n) (G := G) i) := by
-- proof
  intro f g hfg
  ext ⟨q, hq⟩
  have hout := out_card_of_grade q i hq
  have h := congr_fun hfg ⟨q.out, hout⟩
  simp only [embedOrbits] at h
  have hrank : quotientPosetRank n G (Quotient.mk (orbitRel G _) q.out) = i := by
    rw [@quotientPosetRank_mk n G, hout]
  have heq : (⟨q, hq⟩ : { q : QuotientPoset n G // quotientPosetRank n G q = i }) =
    ⟨Quotient.mk (orbitRel G _) q.out, hrank⟩ :=
    Subtype.ext (Quotient.out_eq q).symm
  simp only [heq]
  exact h

end GroupActions

namespace GroupActions

/--
[embedOrbits_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/GroupActions.lean)
-/
@[path]
lemma embedOrbits_invariant
  {n : ℕ}
  {G : Subgroup (Equiv.Perm (Fin n))}
  {i : ℕ}
  {σ : G}
  {S : Finset (Fin n)}
-- given
  (f : { q : QuotientPoset n G // quotientPosetRank n G q = i } → ℝ)
  (hS : S.card = i) :
-- imply
  embedOrbits i f ⟨σ • S, by rw [Finset.card_smul_finset]; exact hS⟩ = embedOrbits i f ⟨S, hS⟩ := by
-- proof
  simp only [embedOrbits]
  congr 1
  exact Subtype.ext (mk_smul_eq σ S)

end GroupActions

namespace GroupActions

/--
[up_invariant_of_embedOrbits](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/GroupActions.lean)
-/
@[path]
lemma up_invariant_of_embedOrbits
  {n : ℕ}
  {G : Subgroup (Equiv.Perm (Fin n))}
  {i : ℕ}
  {T₁ T₂ : BooleanUpDown.Level n (i + 1)}
-- given
  (f : { q : QuotientPoset n G // quotientPosetRank n G q = i } → ℝ)
  (horbit : Quotient.mk (orbitRel G (Finset (Fin n))) T₁.val = Quotient.mk (orbitRel G (Finset (Fin n))) T₂.val) :
-- imply
  BooleanUpDown.up i (embedOrbits i f) T₁ = BooleanUpDown.up i (embedOrbits i f) T₂ := by
-- proof
  obtain ⟨T₁, hT₁⟩ := T₁
  obtain ⟨T₂, hT₂⟩ := T₂
  simp only [BooleanUpDown.up]
  have hrel : (orbitRel G (Finset (Fin n))).r T₁ T₂ := Quotient.exact horbit
  rw [orbitRel_apply] at hrel
  obtain ⟨σ, hσ⟩ := hrel
  change σ • T₂ = T₁ at hσ
  let e : BooleanUpDown.Level n i ≃ BooleanUpDown.Level n i :=
    { toFun := fun ⟨S, hS⟩ => ⟨σ⁻¹ • S, by rw [Finset.card_smul_finset]; exact hS⟩
      invFun := fun ⟨S, hS⟩ => ⟨σ • S, by rw [Finset.card_smul_finset]; exact hS⟩
      left_inv := fun ⟨S, _⟩ => Subtype.ext (smul_inv_smul σ S)
      right_inv := fun ⟨S, _⟩ => Subtype.ext (inv_smul_smul σ S) }
  conv_rhs => rw [← Equiv.sum_comp e]
  congr 1; ext ⟨S, hS_card⟩
  simp only [e, Equiv.coe_fn_mk]
  have hiff : S ⊆ T₁ ↔ σ⁻¹ • S ⊆ T₂ := by
    constructor
    · intro h
      have h1 : σ⁻¹ • S ⊆ σ⁻¹ • T₁ := Finset.smul_finset_subset_smul_finset h
      rwa [show σ⁻¹ • T₁ = T₂ from by rw [← hσ, inv_smul_smul]] at h1
    · intro h
      have h1 : σ • (σ⁻¹ • S) ⊆ σ • T₂ := Finset.smul_finset_subset_smul_finset h
      rwa [smul_inv_smul, hσ] at h1
  simp only [show (S ⊆ T₁) = (σ⁻¹ • S ⊆ T₂) from propext hiff]
  split_ifs
  · exact (embedOrbits_invariant i f σ⁻¹ S hS_card).symm
  · rfl

end GroupActions

namespace GroupActions

/--
[quotientUp_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/GroupActions.lean)
-/
@[path]
lemma quotientUp_injective
  {n : ℕ}
  {G : Subgroup (Equiv.Perm (Fin n))}
  {i : ℕ}
-- given
  (hi : 2 * i + 1 ≤ n) :
-- imply
  Function.Injective (quotientUp (n := n) (G := G) i) := by
-- proof
  intro f g hfg
  apply embedOrbits_injective i
  apply BooleanUpDown.up_injective i (by omega : 2 * i < n)
  ext ⟨T, hT⟩
  set q := Quotient.mk (orbitRel G (Finset (Fin n))) T with hq_def
  have hqrank : quotientPosetRank n G q = i + 1 := by
    rw [hq_def, @quotientPosetRank_mk n G]; exact hT
  have h_at_rep_f := up_invariant_of_embedOrbits i f
    ⟨T, hT⟩ ⟨q.out, out_card_of_grade q (i + 1) hqrank⟩
    (by simp only [hq_def]; exact (Quotient.out_eq q).symm)
  have h_at_rep_g := up_invariant_of_embedOrbits i g
    ⟨T, hT⟩ ⟨q.out, out_card_of_grade q (i + 1) hqrank⟩
    (by simp only [hq_def]; exact (Quotient.out_eq q).symm)
  rw [h_at_rep_f, h_at_rep_g]
  exact congr_fun hfg ⟨q, hqrank⟩

end GroupActions

namespace GroupActions

/--
[quotientUp_isOrderRaising](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/GroupActions.lean)
-/
@[path]
lemma quotientUp_isOrderRaising
  {n : ℕ}
  {G : Subgroup (Equiv.Perm (Fin n))}
  {i : ℕ} :
-- imply
  letI := quotientPoset_gradeMinOrder n G IsOrderRaisingLinearMap (quotientUpLinear (n := n) (G := G) i) (fun (O : { q : QuotientPoset n G // grade ℕ q = i }) (O' : { q : QuotientPoset n G // grade ℕ q = i + 1 }) => O.val < O'.val) := by
-- proof
  letI := quotientPoset_gradeMinOrder n G
  intro O O' hne
  simp only [quotientUpLinear, LinearMap.coe_mk, AddHom.coe_mk,
    quotientUp, BooleanUpDown.up, embedOrbits] at hne
  by_contra h_not_lt
  apply hne
  apply Finset.sum_eq_zero
  intro ⟨S, hS_card⟩ _
  split_ifs with h_sub
  · simp only [Pi.single_apply]
    split_ifs with heq
    · exfalso; apply h_not_lt
      have hS_orbit : Quotient.mk (orbitRel G _) S = O.val := congr_arg Subtype.val heq
      refine ⟨⟨S, O'.val.out, hS_orbit, Quotient.out_eq O'.val, h_sub⟩, ?_⟩
      intro ⟨S', T', hS'eq, hT'eq, hS'T'⟩
      have hcS' : S'.card = i + 1 := by
        have := @quotientPosetRank_mk n G S'; rw [hS'eq] at this; linarith [O'.prop]
      have hcT' : T'.card = i := by
        have := @quotientPosetRank_mk n G T'; rw [hT'eq] at this; linarith [O.prop]
      have := Finset.card_le_card hS'T'
      omega
    · rfl
  · rfl

end GroupActions

namespace GroupActions

/--
[quotientPoset_hasOrderRaisingMatching](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/GroupActions.lean)
-/
@[path]
lemma quotientPoset_hasOrderRaisingMatching
  {n : ℕ}
  {G : Subgroup (Equiv.Perm (Fin n))}
  {i : ℕ}
-- given
  (hi : 2 * i + 1 ≤ n) :
-- imply
  letI := quotientPoset_gradeMinOrder n G letI := quotientPoset_gradedPoset n G HasOrderRaisingMatching (α := QuotientPoset n G) i := by
-- proof
  letI := quotientPoset_gradeMinOrder n G
  letI := quotientPoset_gradedPoset n G
  have hU_inj : Function.Injective (quotientUpLinear (n := n) (G := G) i) := by
    intro f g hfg
    exact quotientUp_injective i hi (show quotientUp i f = quotientUp i g from hfg)
  have hU_ord := quotientUp_isOrderRaising (n := n) (G := G) i
  obtain ⟨μ, hμ_inj, hμ_ord⟩ :=
    order_matching_of_injective_order_raising _ _ hU_inj hU_ord
  refine ⟨fun q => if h : grade ℕ q = i then (μ ⟨q, h⟩).val else q, ?_, ?_, ?_⟩
  · intro x hx; simp only [dif_pos hx]; exact (μ ⟨x, hx⟩).prop
  · intro x hx; simp only [dif_pos hx]; exact hμ_ord ⟨x, hx⟩
  · intro x y hx hy heq
    simp only [dif_pos hx, dif_pos hy] at heq
    exact congr_arg Subtype.val (hμ_inj (Subtype.val_injective heq))

end GroupActions

namespace GroupActions

/--
[quotientPoset_hasOrderLoweringMatching](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/GroupActions.lean)
-/
@[path]
lemma quotientPoset_hasOrderLoweringMatching
  {n : ℕ}
  {G : Subgroup (Equiv.Perm (Fin n))}
  {i : ℕ}
-- given
  (hi : n + 1 ≤ 2 * i)
  (hin : i ≤ n) :
-- imply
  letI := quotientPoset_gradeMinOrder n G letI := quotientPoset_gradedPoset n G HasOrderLoweringMatching (α := QuotientPoset n G) i := by
-- proof
  letI := quotientPoset_gradeMinOrder n G
  letI := quotientPoset_gradedPoset n G
  have hni : 2 * (n - i) + 1 ≤ n := by omega
  obtain ⟨φ, hφ_grade, hφ_lt, hφ_inj⟩ := quotientPoset_hasOrderRaisingMatching (n - i) hni
  let ψ : QuotientPoset n G → QuotientPoset n G :=
    fun q => quotientPosetCompl (φ (quotientPosetCompl q))
  refine ⟨ψ, ?_, ?_, ?_⟩
  · intro x hx
    show grade ℕ (ψ x) = i - 1
    simp only [ψ]
    have hc : grade ℕ (quotientPosetCompl x) = n - i := by
      rw [quotientPosetCompl_grade']; omega
    rw [quotientPosetCompl_grade', hφ_grade _ hc]; omega
  · intro x hx
    show ψ x < x
    simp only [ψ]
    have hc : grade ℕ (quotientPosetCompl x) = n - i := by
      rw [quotientPosetCompl_grade']; omega
    have h1 : quotientPosetCompl x < φ (quotientPosetCompl x) := hφ_lt _ hc
    have h2 := quotientPosetCompl_strictAnti h1
    rwa [quotientPosetCompl_involutive] at h2
  · intro x y hx hy heq
    show x = y
    simp only [ψ] at heq
    have hc1 : grade ℕ (quotientPosetCompl x) = n - i := by
      rw [quotientPosetCompl_grade']; omega
    have hc2 : grade ℕ (quotientPosetCompl y) = n - i := by
      rw [quotientPosetCompl_grade']; omega
    exact quotientPosetCompl_injective
      (hφ_inj _ _ hc1 hc2 (quotientPosetCompl_injective heq))

end GroupActions

namespace GroupActions

/--
[quotientPoset_hasOrderMatchings](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/GroupActions.lean)
-/
@[path]
lemma quotientPoset_hasOrderMatchings
  {n : ℕ}
  {G : Subgroup (Equiv.Perm (Fin n))} :
-- imply
  letI := quotientPoset_gradeMinOrder n G letI := quotientPoset_gradedPoset n G HasOrderMatchings (α := QuotientPoset n G) (n / 2) := by
-- proof
  letI := quotientPoset_gradeMinOrder n G
  letI := quotientPoset_gradedPoset n G
  refine ⟨Nat.div_le_self n 2, ?_, ?_⟩
  · intro i hi; exact quotientPoset_hasOrderRaisingMatching i (by omega)
  · intro i hi hin; exact quotientPoset_hasOrderLoweringMatching i (by omega) hin

end GroupActions

namespace GroupActions

/--
[boolean_quotient_unimodal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/GroupActions.lean)
-/
@[path]
lemma boolean_quotient_unimodal
  {n : ℕ}
  {G : Subgroup (Equiv.Perm (Fin n))} :
-- imply
  letI := quotientPoset_gradeMinOrder n G letI := quotientPoset_gradedPoset n G IsRankUnimodal (α := QuotientPoset n G) := by
-- proof
  letI := quotientPoset_gradeMinOrder n G
  letI := quotientPoset_gradedPoset n G
  exact orderMatchings_imp_unimodal (n / 2) quotientPoset_hasOrderMatchings

end GroupActions

namespace GroupActions

/--
[boolean_quotient_sperner](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/GroupActions.lean)
-/
@[path]
lemma boolean_quotient_sperner
  {n : ℕ}
  {G : Subgroup (Equiv.Perm (Fin n))} :
-- imply
  letI := quotientPoset_gradeMinOrder n G letI := quotientPoset_gradedPoset n G HasSpernerProperty (α := QuotientPoset n G) := by
-- proof
  letI := quotientPoset_gradeMinOrder n G
  letI := quotientPoset_gradedPoset n G
  exact orderMatchings_imp_sperner (n / 2) quotientPoset_hasOrderMatchings
end GroupActions
namespace GraphIsoPoset
open SpernerProperty GroupActions


namespace GraphIsoPoset

/--
[graph_sequence_symmetric](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/GroupActions.lean)
-/
@[path]
lemma graph_sequence_symmetric
  {m : ℕ} :
-- imply
  letI := quotientPoset_gradeMinOrder (edgeCount m) (graphIsoGroup m) letI := quotientPoset_gradedPoset (edgeCount m) (graphIsoGroup m) IsRankSymmetric (α := GraphPoset m) :=
-- proof
  quotientPoset_isRankSymmetric (edgeCount m) (graphIsoGroup m)

end GraphIsoPoset

namespace GraphIsoPoset

/--
[graph_sequence_unimodal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/GroupActions.lean)
-/
@[path]
lemma graph_sequence_unimodal
  {m : ℕ} :
-- imply
  letI := quotientPoset_gradeMinOrder (edgeCount m) (graphIsoGroup m) letI := quotientPoset_gradedPoset (edgeCount m) (graphIsoGroup m) IsRankUnimodal (α := GraphPoset m) :=
-- proof
  boolean_quotient_unimodal

end GraphIsoPoset

namespace GraphIsoPoset

/--
[graph_poset_sperner](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/GroupActions.lean)
-/
@[path]
lemma graph_poset_sperner
  {m : ℕ} :
-- imply
  letI := quotientPoset_gradeMinOrder (edgeCount m) (graphIsoGroup m) letI := quotientPoset_gradedPoset (edgeCount m) (graphIsoGroup m) HasSpernerProperty (α := GraphPoset m) :=
-- proof
  boolean_quotient_sperner

end GraphIsoPoset

namespace GraphIsoPoset

/--
[maxRankCount_eq_middle_of_symmetric_unimodal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/GroupActions.lean)
-/
@[path]
lemma maxRankCount_eq_middle_of_symmetric_unimodal
  [PartialOrder α]
  [Fintype α]
  [DecidableEq α]
  [GradeMinOrder ℕ α]
  [GradedPoset α]
-- given
  (hsym : IsRankSymmetric (α := α))
  (huni : IsRankUnimodal (α := α)) :
-- imply
  maxRankCount (α := α) = rankCount (α := α) (GradedPoset.rank (α := α) / 2) := by
-- proof
  obtain ⟨j, hj, hinc, hdec⟩ := huni
  set n := GradedPoset.rank (α := α)
  have hj_max : ∀ i, i ≤ n → rankCount (α := α) i ≤ rankCount (α := α) j := by
    intro i hi
    by_cases hij : i ≤ j
    · exact hinc i j hij le_rfl
    · push_neg at hij
      exact hdec j i le_rfl (le_of_lt hij) hi
  have hmax_eq_j : maxRankCount (α := α) = rankCount (α := α) j := by
    apply le_antisymm
    ·
      unfold maxRankCount
      apply Finset.sup_le
      intro i hi
      rw [Finset.mem_range] at hi
      exact hj_max i (by omega)
    ·
      exact rankCount_le_maxRankCount j hj
  suffices h : rankCount (α := α) (n / 2) = rankCount (α := α) j by
    rw [hmax_eq_j, h]
  apply le_antisymm
  ·
    exact hj_max (n / 2) (Nat.div_le_self n 2)
  ·
    have hsym_j : rankCount (α := α) (n - j) = rankCount (α := α) j :=
      (hsym j hj).symm
    rw [← hsym_j]
    by_cases hjn : j ≤ n / 2
    ·
      exact hdec (n / 2) (n - j) (by omega) (by omega) (by omega)
    ·
      push_neg at hjn
      exact hinc (n - j) (n / 2) (by omega) (by omega)

end GraphIsoPoset

namespace GraphIsoPoset

/--
[graph_poset_max_antichain_level](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/GroupActions.lean)
-/
@[path]
lemma graph_poset_max_antichain_level
  {m : ℕ} :
-- imply
  letI := quotientPoset_gradeMinOrder (edgeCount m) (graphIsoGroup m) letI := quotientPoset_gradedPoset (edgeCount m) (graphIsoGroup m) maxRankCount (α := GraphPoset m) = rankCount (α := GraphPoset m) (edgeCount m / 2) := by
-- proof
  letI := quotientPoset_gradeMinOrder (edgeCount m) (graphIsoGroup m)
  letI := quotientPoset_gradedPoset (edgeCount m) (graphIsoGroup m)
  exact maxRankCount_eq_middle_of_symmetric_unimodal
    (graph_sequence_symmetric m) (graph_sequence_unimodal m)

end GraphIsoPoset

/--
[out_card_of_grade](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/GroupActions.lean)
-/
@[path]
private lemma out_card_of_grade_eq
  {n : ℕ}
  {G : Subgroup (Equiv.Perm (Fin n))}
  {q : QuotientPoset n G}
  {i : ℕ}
-- given
  (hq : quotientPosetRank n G q = i) :
-- imply
  q.out.card = i := by
-- proof
  apply GroupActions.out_card_of_grade q i hq

/--
[card_edgeSubsets](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/GroupActions.lean)
-/
@[path]
private lemma card_edgeSubsets_eq
  {m : ℕ}
  {m : ℕ} :
-- imply
  Fintype.card (EdgeSubsets m) = edgeCount m := by
-- proof
  apply GraphIsoPoset.card_edgeSubsets m


-- created on 2026-10-23

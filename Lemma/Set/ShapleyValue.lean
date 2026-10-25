import Mathlib
import sympy.Basic
import Theorem.GameTheory.ShapleyValue.Part3
open MathlibExt.GameTheory.ShapleyValue


namespace MathlibExt.GameTheory.ShapleyValue

variable [DecidableEq Player] [Fintype Player]
/--
[unanimity_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/ShapleyValue.lean)
-/
@[path]
omit [Fintype Player] in
private lemma unanimity_zero : unanimity (∅ : Finset Player) = 0 := by
  simp [unanimity]

end MathlibExt.GameTheory.ShapleyValue

namespace MathlibExt.GameTheory.ShapleyValue

variable [DecidableEq Player] [Fintype Player]
/--
[unanimity_charFun](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/ShapleyValue.lean)
-/
@[path]
omit [Fintype Player] in
private lemma unanimity_charFun {T : Finset Player} (hT : T ≠ ∅) (S : Set Player) :
  (unanimity T).charFun S = if (T : Set Player) ⊆ S then (1 : ℝ) else 0 := by
  classical
  simp [unanimity, dite_eq_right hT]

end MathlibExt.GameTheory.ShapleyValue

namespace MathlibExt.GameTheory.ShapleyValue

variable [DecidableEq Player] [Fintype Player]
/--
[charFun_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/ShapleyValue.lean)
-/
@[path]
omit [DecidableEq Player] [Fintype Player] in
private lemma charFun_zero (S : Set Player) : (0 : CoopGame Player).charFun S = 0 :=
  rfl

end MathlibExt.GameTheory.ShapleyValue

namespace MathlibExt.GameTheory.ShapleyValue

variable [DecidableEq Player] [Fintype Player]
/--
[mobiusCoeff_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/ShapleyValue.lean)
-/
@[path]
omit [DecidableEq Player] [Fintype Player] in
private lemma mobiusCoeff_empty (v : CoopGame Player) : mobiusCoeff v ∅ = 0 := by
  simp [mobiusCoeff, Finset.powerset_empty, Finset.coe_empty, v.empty]

end MathlibExt.GameTheory.ShapleyValue

namespace MathlibExt.GameTheory.ShapleyValue

variable [DecidableEq Player] [Fintype Player]
/--
[sum_powerset_neg_one_pow_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/ShapleyValue.lean)
-/
@[path]
omit [Fintype Player] in
private lemma sum_powerset_neg_one_pow_card (M : Finset Player) :
  ∑ U ∈ M.powerset, (-1 : ℝ) ^ U.card = (if M = ∅ then 1 else 0) := by
  by_cases hM : M = ∅
  · subst hM
    simp [Finset.powerset_empty]
  · have h := Finset.prod_add (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)) M
    simp only [Finset.prod_const, mul_one, one_pow] at h
    have hne : M.Nonempty := Finset.nonempty_iff_ne_empty.mpr hM
    have hcard : M.card ≠ 0 := Finset.card_ne_zero.mpr hne
    have hbase : (-1 : ℝ) + 1 = 0 := by ring
    rw [hbase, zero_pow hcard] at h
    rwa [ite_eq_right hM]

end MathlibExt.GameTheory.ShapleyValue

namespace MathlibExt.GameTheory.ShapleyValue

variable [DecidableEq Player] [Fintype Player]
/--
[card_sdiff_of_subset](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/ShapleyValue.lean)
-/
@[path]
omit [Fintype Player] in
private lemma card_sdiff_of_subset {R T : Finset Player} (h : R ⊆ T) :
  (T \ R).card = T.card - R.card := by
  have h1 : R ∩ T = R := by
    ext x
    simp only [Finset.mem_inter]
    constructor
    · intro hx; exact hx.1
    · intro hx; exact ⟨hx, h hx⟩
  rw [Finset.card_sdiff, h1]

end MathlibExt.GameTheory.ShapleyValue

namespace MathlibExt.GameTheory.ShapleyValue

variable [DecidableEq Player] [Fintype Player]
/--
[inner_mobius_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/ShapleyValue.lean)
-/
@[path]
omit [Fintype Player] in
private lemma inner_mobius_sum (S R : Finset Player) (hR : R ∈ S.powerset) :
  ∑ T ∈ S.powerset.filter (fun T => R ⊆ T), (-1 : ℝ) ^ (T.card - R.card)
    = (if R = S then 1 else 0) := by
  have hRS : R ⊆ S := Finset.mem_powerset.mp hR
  have hsum : ∑ T ∈ S.powerset.filter (fun T => R ⊆ T), (-1 : ℝ) ^ (T.card - R.card)
    = ∑ U ∈ (S \ R).powerset, (-1 : ℝ) ^ U.card := by
    apply Finset.sum_bij (fun T _ => T \ R)
    · intro T hT
      show T \ R ∈ (S \ R).powerset
      rw [Finset.mem_filter] at hT
      rw [Finset.mem_powerset]
      exact Finset.sdiff_subset_sdiff (Finset.mem_powerset.mp hT.1) (fun _ h => h)
    · intro T₁ hT₁ T₂ hT₂ hEq
      rw [Finset.mem_filter] at hT₁ hT₂
      change T₁ \ R = T₂ \ R at hEq
      have e1 := Finset.sdiff_union_of_subset hT₁.2
      have e2 := Finset.sdiff_union_of_subset hT₂.2
      rw [← e1, ← e2, hEq]
    · intro U hU
      rw [Finset.mem_powerset] at hU
      refine ⟨U ∪ R, ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_powerset]
        constructor
        · exact Finset.union_subset (fun x hx => Finset.sdiff_subset (hU hx)) hRS
        · exact Finset.subset_union_right
      · show (U ∪ R) \ R = U
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_union]
        have hxR : x ∈ U → x ∉ R := by
          intro hxU
          have hxSR := hU hxU
          rwa [Finset.mem_sdiff] at hxSR
        constructor
        · rintro ⟨hU | hR, hnR⟩
          · exact hU
          · exact absurd hR hnR
        · intro hxU
          exact ⟨Or.inl hxU, hxR hxU⟩
    · intro T hT
      rw [Finset.mem_filter] at hT
      show (-1 : ℝ) ^ (T.card - R.card) = (-1 : ℝ) ^ (T \ R).card
      rw [card_sdiff_of_subset hT.2]
  rw [hsum, sum_powerset_neg_one_pow_card]
  have hiff : (S \ R = ∅) ↔ (R = S) := by
    constructor
    · intro h
      exact subset_antisymm hRS (Finset.sdiff_eq_empty_iff_subset.mp h)
    · intro h
      subst h
      exact Finset.sdiff_self R
  simp only [hiff]

end MathlibExt.GameTheory.ShapleyValue

namespace MathlibExt.GameTheory.ShapleyValue

variable [DecidableEq Player] [Fintype Player]
/--
[mobius_inversion](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/ShapleyValue.lean)
-/
@[path]
omit [DecidableEq Player] [Fintype Player] in
private lemma mobius_inversion (v : CoopGame Player) (S : Finset Player) :
  v.charFun ↑S = ∑ T ∈ S.powerset, mobiusCoeff v T := by
  classical
  have hTeq : ∀ T ∈ S.powerset, T.powerset = S.powerset.filter (fun R => R ⊆ T) := by
    intro T hT
    have hTS : T ⊆ S := Finset.mem_powerset.mp hT
    ext R
    simp only [Finset.mem_powerset, Finset.mem_filter]
    constructor
    · intro hRT; exact ⟨fun x hx => hTS (hRT hx), hRT⟩
    · intro h; exact h.2
  have hexpand : ∀ T ∈ S.powerset, mobiusCoeff v T
    = ∑ R ∈ S.powerset,
      (if R ⊆ T then (-1 : ℝ) ^ (T.card - R.card) * v.charFun ↑R else 0) := by
    intro T hT
    unfold mobiusCoeff
    rw [hTeq T hT, Finset.sum_filter]
  have hinner : ∀ R ∈ S.powerset, (∑ T ∈ S.powerset,
    (if R ⊆ T then (-1 : ℝ) ^ (T.card - R.card) * v.charFun ↑R else 0))
    = (if R = S then (1 : ℝ) else 0) * v.charFun ↑R := by
    intro R hR
    rw [← Finset.sum_filter, ← Finset.sum_mul, inner_mobius_sum S R hR]
  have hfinal : (∑ R ∈ S.powerset, (if R = S then (1 : ℝ) else 0) * v.charFun ↑R)
    = v.charFun ↑S := by
    have hterm : ∀ R ∈ S.powerset, ((if R = S then (1 : ℝ) else 0) * v.charFun ↑R)
      = (if R = S then v.charFun ↑R else 0) := by
      intro R _
      by_cases h : R = S
      · subst h; simp
      · simp [h]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
    rw [ite_eq_left (Finset.mem_powerset.mpr (fun _ h => h))]
  symm
  calc ∑ T ∈ S.powerset, mobiusCoeff v T
    = ∑ T ∈ S.powerset, ∑ R ∈ S.powerset,
      (if R ⊆ T then (-1 : ℝ) ^ (T.card - R.card) * v.charFun ↑R else 0) :=
      Finset.sum_congr rfl hexpand
    _ = ∑ R ∈ S.powerset, ∑ T ∈ S.powerset,
      (if R ⊆ T then (-1 : ℝ) ^ (T.card - R.card) * v.charFun ↑R else 0) :=
      Finset.sum_comm
    _ = ∑ R ∈ S.powerset, ((if R = S then (1 : ℝ) else 0) * v.charFun ↑R) :=
      Finset.sum_congr rfl hinner
    _ = v.charFun ↑S := hfinal

end MathlibExt.GameTheory.ShapleyValue

namespace MathlibExt.GameTheory.ShapleyValue

variable [DecidableEq Player] [Fintype Player]
/--
[unanimity_null_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/ShapleyValue.lean)
-/
@[path]
omit [Fintype Player] in
private lemma unanimity_null_of_not_mem {T : Finset Player} (hT : T ≠ ∅) {i : Player}
  (hi : i ∉ T) : IsNullPlayer (unanimity T) i := by
  classical
  intro S _
  rw [unanimity_charFun hT, unanimity_charFun hT]
  have hiff : ((T : Set Player) ⊆ insert i S) ↔ ((T : Set Player) ⊆ S) := by
    constructor
    · intro h t ht
      have htT : t ∈ T := Finset.mem_coe.mp ht
      have hne : t ≠ i := fun heq => hi (heq ▸ htT)
      have hmem := h ht
      simp only [Set.mem_insert_iff] at hmem
      cases hmem with
      | inl heq => exact absurd heq hne
      | inr hm => exact hm
    · intro h t ht
      exact Set.mem_insert_of_mem i (h ht)
  rw [hiff]

end MathlibExt.GameTheory.ShapleyValue

namespace MathlibExt.GameTheory.ShapleyValue

variable [DecidableEq Player] [Fintype Player]
/--
[unanimity_swap_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/ShapleyValue.lean)
-/
@[path]
omit [Fintype Player] in
private lemma unanimity_swap_invariant {T : Finset Player} (hT : T ≠ ∅) {i j : Player}
  (hi : i ∈ T) (hj : j ∈ T) (S : Set Player) :
  (unanimity T).charFun ((Equiv.swap i j) '' S) = (unanimity T).charFun S := by
  classical
  rw [unanimity_charFun hT, unanimity_charFun hT]
  have hpres : ∀ t : Player, t ∈ T → (Equiv.swap i j) t ∈ T := by
    intro t ht
    by_cases hti : t = i
    · subst hti
      rwa [Equiv.swap_apply_left]
    · by_cases htj : t = j
      · subst htj
        rwa [Equiv.swap_apply_right]
      · rw [Equiv.swap_apply_of_ne_of_ne hti htj]
        exact ht
  have hpres_symm : ∀ t : Player, t ∈ T → (Equiv.swap i j).symm t ∈ T := by
    intro t ht
    rw [Equiv.symm_swap]
    exact hpres t ht
  have hiff : ((T : Set Player) ⊆ (Equiv.swap i j) '' S) ↔ ((T : Set Player) ⊆ S) := by
    constructor
    · intro h t ht
      have htT : t ∈ T := Finset.mem_coe.mp ht
      have hst : (Equiv.swap i j) t ∈ (T : Set Player) :=
        Finset.mem_coe.mpr (hpres t htT)
      obtain ⟨s, hs, hσ⟩ := h hst
      have heq : s = t := Equiv.injective (Equiv.swap i j) hσ
      subst heq
      exact hs
    · intro h t ht
      have htT : t ∈ T := Finset.mem_coe.mp ht
      have hsymT : (Equiv.swap i j).symm t ∈ T := hpres_symm t htT
      have hsS : (Equiv.swap i j).symm t ∈ S := h (Finset.mem_coe.mpr hsymT)
      exact ⟨(Equiv.swap i j).symm t, hsS, Equiv.apply_symm_apply _ _⟩
  rw [hiff]

end MathlibExt.GameTheory.ShapleyValue

namespace MathlibExt.GameTheory.ShapleyValue

variable [DecidableEq Player] [Fintype Player]
/--
[forced_unanimity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/ShapleyValue.lean)
-/
@[path]
private lemma forced_unanimity (φ : CoopGame Player →ₗ[ℝ] (Player → ℝ))
  (heff : IsEfficient φ) (hsymm : IsSymmetric φ)
  (hnull : SatisfiesNullPlayerAxiom φ)
  (T : Finset Player) (hT : T ≠ ∅) (i : Player) :
  φ (unanimity T) i = if i ∈ T then 1 / (T.card : ℝ) else 0 := by
  classical
  have hnull_all : ∀ j : Player, j ∉ T → φ (unanimity T) j = 0 := by
    intro j hj
    exact hnull _ j (unanimity_null_of_not_mem hT hj)
  have hsym_all : ∀ a b : Player, a ∈ T → b ∈ T →
    φ (unanimity T) a = φ (unanimity T) b := by
    intro a b ha hb
    have hinv : ∀ S : Set Player,
      (unanimity T).charFun ((Equiv.swap a b) '' S) = (unanimity T).charFun S :=
      fun S => unanimity_swap_invariant hT ha hb S
    have hswap := hsymm (Equiv.swap a b) (unanimity T) hinv a
    rwa [Equiv.swap_apply_left] at hswap
  have heff_one : ∑ j : Player, φ (unanimity T) j = 1 := by
    have he := heff (unanimity T)
    have hsub : ((T : Set Player) ⊆ Set.univ) := Set.subset_univ _
    have hchar : (unanimity T).charFun Set.univ = 1 := by
      rw [unanimity_charFun hT]
      simp [hsub]
    rwa [hchar] at he
  obtain ⟨j0, hj0⟩ := Finset.nonempty_iff_ne_empty.mpr hT
  have hcard_ne0 : T.card ≠ 0 := Finset.card_ne_zero.mpr ⟨j0, hj0⟩
  have hsum_T : ∑ j ∈ T, φ (unanimity T) j = 1 := by
    have hsub : T ⊆ Finset.univ := Finset.subset_univ T
    have hzero : ∀ x : Player, x ∈ Finset.univ → x ∉ T → φ (unanimity T) x = 0 :=
      fun x _ hx => hnull_all x hx
    have h := Finset.sum_subset hsub hzero
    have huniv : (∑ x ∈ Finset.univ, φ (unanimity T) x) = 1 := heff_one
    rwa [huniv] at h
  have hconst : ∀ j : Player, j ∈ T → φ (unanimity T) j = φ (unanimity T) j0 :=
    fun j hj => hsym_all j j0 hj hj0
  have hsum_const : (∑ j ∈ T, φ (unanimity T) j)
    = (T.card : ℝ) * φ (unanimity T) j0 := by
    have h1 : (∑ j ∈ T, φ (unanimity T) j)
      = ∑ _j ∈ T, φ (unanimity T) j0 := Finset.sum_congr rfl hconst
    rw [h1, Finset.sum_const, nsmul_eq_mul]
  have hmul : (T.card : ℝ) * φ (unanimity T) j0 = 1 := by
    rw [← hsum_const, hsum_T]
  have hj0_eq : φ (unanimity T) j0 = 1 / (T.card : ℝ) := by
    have hmul' : φ (unanimity T) j0 * (T.card : ℝ) = 1 := by
      rwa [mul_comm]
    exact eq_one_div_of_mul_eq_one_left hmul'
  by_cases hiT : i ∈ T
  · have hi_eq : φ (unanimity T) i = φ (unanimity T) j0 :=
    hsym_all i j0 hiT hj0
    rw [hi_eq, hj0_eq, ite_eq_left hiT]
  · rw [hnull_all i hiT, ite_eq_right hiT]

end MathlibExt.GameTheory.ShapleyValue

namespace MathlibExt.GameTheory.ShapleyValue

variable [DecidableEq Player] [Fintype Player]
/--
[agree_on_unanimity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/ShapleyValue.lean)
-/
@[path]
private lemma agree_on_unanimity (φ₁ φ₂ : CoopGame Player →ₗ[ℝ] (Player → ℝ))
  (h1e : IsEfficient φ₁) (h1s : IsSymmetric φ₁)
  (h1n : SatisfiesNullPlayerAxiom φ₁)
  (h2e : IsEfficient φ₂) (h2s : IsSymmetric φ₂)
  (h2n : SatisfiesNullPlayerAxiom φ₂)
  (T : Finset Player) : φ₁ (unanimity T) = φ₂ (unanimity T) := by
  funext i
  by_cases hT : T = ∅
  · subst hT
    rw [unanimity_zero, map_zero, map_zero]
  · rw [forced_unanimity φ₁ h1e h1s h1n T hT i,
    forced_unanimity φ₂ h2e h2s h2n T hT i]

end MathlibExt.GameTheory.ShapleyValue

namespace MathlibExt.GameTheory.ShapleyValue

variable [DecidableEq Player] [Fintype Player]
/--
[shapleyLM_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/ShapleyValue.lean)
-/
@[path]
private lemma shapleyLM_apply (v : CoopGame Player) (i : Player) :
  shapleyLM v i = ∑ T ∈ Finset.univ.powerset.filter (fun T => i ∈ T),
    mobiusCoeff v T / (T.card : ℝ) :=
  rfl

end MathlibExt.GameTheory.ShapleyValue

namespace MathlibExt.GameTheory.ShapleyValue

variable [DecidableEq Player] [Fintype Player]
/--
[shapley_inner_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/ShapleyValue.lean)
-/
@[path]
private lemma shapley_inner_sum (v : CoopGame Player) (T : Finset Player) :
  (∑ i ∈ Finset.univ, (if i ∈ T then mobiusCoeff v T / (T.card : ℝ) else 0))
    = mobiusCoeff v T := by
  by_cases hT : T = ∅
  · subst hT
    have hzero : ∀ i ∈ Finset.univ,
      (if i ∈ (∅ : Finset Player) then
        mobiusCoeff v ∅ / ((∅ : Finset Player).card : ℝ) else 0) = 0 := by
      intro i _
      simp
    rw [Finset.sum_congr rfl hzero]
    rw [Finset.sum_const_zero, mobiusCoeff_empty]
  · have hcard_ne : (T.card : ℝ) ≠ 0 := by
    have hne : T.card ≠ 0 :=
      Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hT)
    exact Nat.cast_ne_zero.mpr hne
    have hfilter : Finset.univ.filter (fun i => i ∈ T) = T := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hrewrite :
      (∑ i ∈ Finset.univ, (if i ∈ T then mobiusCoeff v T / (T.card : ℝ) else 0))
      = ∑ _i ∈ T, mobiusCoeff v T / (T.card : ℝ) := by
      rw [← Finset.sum_filter, hfilter]
    rw [hrewrite, Finset.sum_const, nsmul_eq_mul]
    exact mul_div_cancel₀ _ hcard_ne

end MathlibExt.GameTheory.ShapleyValue

namespace MathlibExt.GameTheory.ShapleyValue

variable [DecidableEq Player] [Fintype Player]
/--
[shapley_efficient](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/ShapleyValue.lean)
-/
@[path]
private lemma shapley_efficient :
  IsEfficient (shapleyLM : CoopGame Player →ₗ[ℝ] (Player → ℝ)) := by
  intro v
  show (∑ i : Player, shapleyLM v i) = v.charFun Set.univ
  have hstep1 : (∑ i : Player, shapleyLM v i)
    = ∑ i ∈ Finset.univ, ∑ T ∈ Finset.univ.powerset,
      (if i ∈ T then mobiusCoeff v T / (T.card : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [shapleyLM_apply]
    exact Finset.sum_filter _ _
  have hstep2 : (∑ i ∈ Finset.univ, ∑ T ∈ Finset.univ.powerset,
    (if i ∈ T then mobiusCoeff v T / (T.card : ℝ) else 0))
    = ∑ T ∈ Finset.univ.powerset, ∑ i ∈ Finset.univ,
      (if i ∈ T then mobiusCoeff v T / (T.card : ℝ) else 0) :=
    Finset.sum_comm
  have hstep3 : (∑ T ∈ Finset.univ.powerset, ∑ i ∈ Finset.univ,
    (if i ∈ T then mobiusCoeff v T / (T.card : ℝ) else 0))
    = ∑ T ∈ Finset.univ.powerset, mobiusCoeff v T := by
    apply Finset.sum_congr rfl
    intro T _
    exact shapley_inner_sum v T
  have hstep4 : (∑ T ∈ Finset.univ.powerset, mobiusCoeff v T)
    = v.charFun Set.univ := by
    have hinv := mobius_inversion v Finset.univ
    rwa [Finset.coe_univ] at hinv
  rw [hstep1, hstep2, hstep3, hstep4]

end MathlibExt.GameTheory.ShapleyValue

namespace MathlibExt.GameTheory.ShapleyValue

variable [DecidableEq Player] [Fintype Player]
/--
[mobiusCoeff_eq_zero_of_null](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/ShapleyValue.lean)
-/
@[path]
omit [DecidableEq Player] [Fintype Player] in
private lemma mobiusCoeff_eq_zero_of_null (v : CoopGame Player) (i : Player)
  (hnull : IsNullPlayer v i) (T : Finset Player) (hiT : i ∈ T) :
  mobiusCoeff v T = 0 := by
  classical
  have hterm : ∀ R ∈ T.powerset.filter (fun R => i ∉ R),
    (-1 : ℝ) ^ (T.card - (insert i R).card) * v.charFun ↑(insert i R)
    = -((-1 : ℝ) ^ (T.card - R.card) * v.charFun ↑R) := by
    intro R hR
    rw [Finset.mem_filter] at hR
    have hRT : R ⊆ T := Finset.mem_powerset.mp hR.1
    have hiR : i ∉ R := hR.2
    have hcard : (insert i R).card = R.card + 1 :=
      Finset.card_insert_of_notMem hiR
    have hne : R ≠ T := by
      intro heq
      subst heq
      exact hiR hiT
    have hlt : R.card < T.card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hRT, hne⟩)
    have hle : 1 ≤ T.card - R.card := by omega
    have hexp2 : T.card - (insert i R).card = T.card - R.card - 1 := by
      rw [hcard]
      omega
    have hchar : v.charFun ↑(insert i R) = v.charFun ↑R := by
      rw [Finset.coe_insert]
      have hiS : i ∉ (↑R : Set Player) := fun h => hiR (Finset.mem_coe.mp h)
      exact hnull ↑R hiS
    have hpow : (-1 : ℝ) ^ (T.card - (insert i R).card)
      = -(-1 : ℝ) ^ (T.card - R.card) := by
      rw [hexp2]
      have hm : T.card - R.card - 1 + 1 = T.card - R.card :=
        Nat.sub_add_cancel hle
      have hpow_eq : (-1 : ℝ) ^ (T.card - R.card)
        = (-1 : ℝ) ^ (T.card - R.card - 1) * (-1) := by
        conv_lhs => rw [← hm, pow_succ]
      have hneg : (-1 : ℝ) ^ (T.card - R.card - 1) * (-1)
        = -(-1 : ℝ) ^ (T.card - R.card - 1) := by ring
      rw [hneg] at hpow_eq
      have h2 := congrArg (fun x : ℝ => -x) hpow_eq
      simp only [neg_neg] at h2
      exact h2.symm
    rw [hchar, hpow]
    ring
  have hreindex : (∑ R ∈ T.powerset.filter (fun R => i ∉ R),
    (-1 : ℝ) ^ (T.card - (insert i R).card) * v.charFun ↑(insert i R))
    = ∑ R' ∈ T.powerset.filter (fun R' => i ∈ R'),
      (-1 : ℝ) ^ (T.card - R'.card) * v.charFun ↑R' := by
    apply Finset.sum_bij (fun R _ => insert i R)
    · intro R hR
      rw [Finset.mem_filter] at hR ⊢
      have hRT : R ⊆ T := Finset.mem_powerset.mp hR.1
      constructor
      · rw [Finset.mem_powerset]
        rw [Finset.insert_subset_iff]
        exact ⟨hiT, hRT⟩
      · exact Finset.mem_insert_self i R
    · intro R₁ hR₁ R₂ hR₂ hEq
      rw [Finset.mem_filter] at hR₁ hR₂
      have e1 := Finset.erase_insert hR₁.2
      have e2 := Finset.erase_insert hR₂.2
      have h := congrArg (fun S => S.erase i) hEq
      rwa [e1, e2] at h
    · intro R' hR'
      rw [Finset.mem_filter] at hR'
      have hRT' : R' ⊆ T := Finset.mem_powerset.mp hR'.1
      have hiR' : i ∈ R' := hR'.2
      refine ⟨R'.erase i, ?_, ?_⟩
      · rw [Finset.mem_filter]
        constructor
        · rw [Finset.mem_powerset]
          exact (Finset.erase_subset i R').trans hRT'
        · exact Finset.notMem_erase i R'
      · exact Finset.insert_erase hiR'
    · intro R _
      rfl
  have hsum_eq : (∑ R' ∈ T.powerset.filter (fun R' => i ∈ R'),
    (-1 : ℝ) ^ (T.card - R'.card) * v.charFun ↑R')
    = ∑ R ∈ T.powerset.filter (fun R => i ∉ R),
      -((-1 : ℝ) ^ (T.card - R.card) * v.charFun ↑R) := by
    rw [← hreindex]
    apply Finset.sum_congr rfl
    intro R hR
    exact hterm R hR
  have hneg : (∑ R' ∈ T.powerset.filter (fun R' => i ∈ R'),
    (-1 : ℝ) ^ (T.card - R'.card) * v.charFun ↑R')
    = -(∑ R ∈ T.powerset.filter (fun R => i ∉ R),
      (-1 : ℝ) ^ (T.card - R.card) * v.charFun ↑R) := by
    rw [hsum_eq]
    exact Finset.sum_neg_distrib _
  unfold mobiusCoeff
  have hsplit := Finset.sum_filter_add_sum_filter_not T.powerset
    (fun R => i ∈ R)
    (fun R => (-1 : ℝ) ^ (T.card - R.card) * v.charFun ↑R)
  rw [← hsplit, hneg]
  exact neg_add_cancel _

end MathlibExt.GameTheory.ShapleyValue

namespace MathlibExt.GameTheory.ShapleyValue

variable [DecidableEq Player] [Fintype Player]
/--
[shapley_null](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/ShapleyValue.lean)
-/
@[path]
private lemma shapley_null : SatisfiesNullPlayerAxiom
  (shapleyLM : CoopGame Player →ₗ[ℝ] (Player → ℝ)) := by
  intro v i hnull
  rw [shapleyLM_apply]
  apply Finset.sum_eq_zero
  intro T hT
  rw [Finset.mem_filter] at hT
  have hcz : mobiusCoeff v T = 0 :=
    mobiusCoeff_eq_zero_of_null v i hnull T hT.2
  rw [hcz, zero_div]

end MathlibExt.GameTheory.ShapleyValue

namespace MathlibExt.GameTheory.ShapleyValue

variable [DecidableEq Player] [Fintype Player]
/--
[mobiusCoeff_perm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/ShapleyValue.lean)
-/
@[path]
omit [Fintype Player] in
private lemma mobiusCoeff_perm (σ : Equiv.Perm Player) (v : CoopGame Player)
  (hinv : ∀ S : Set Player, v.charFun (σ '' S) = v.charFun S)
  (T : Finset Player) :
  mobiusCoeff v (Finset.image (⇑σ) T) = mobiusCoeff v T := by
  unfold mobiusCoeff
  have hinj : Function.Injective (⇑σ) := Equiv.injective σ
  have hcardT : (Finset.image (⇑σ) T).card = T.card :=
    Finset.card_image_of_injective T hinj
  have hpowerset : (Finset.image (⇑σ) T).powerset
    = Finset.image (fun R => Finset.image (⇑σ) R) T.powerset :=
    Finset.powerset_image
  rw [hpowerset]
  have hinjOn : Set.InjOn (fun R => Finset.image (⇑σ) R) ↑(T.powerset) := by
    apply Set.injOn_of_injective
    exact Finset.image_injective hinj
  rw [Finset.sum_image hinjOn]
  apply Finset.sum_congr rfl
  intro R _
  have hcardR : (Finset.image (⇑σ) R).card = R.card :=
    Finset.card_image_of_injective R hinj
  have hchar : v.charFun ↑(Finset.image (⇑σ) R) = v.charFun ↑R := by
    rw [Finset.coe_image]
    exact hinv ↑R
  rw [hcardT, hcardR, hchar]

end MathlibExt.GameTheory.ShapleyValue

namespace MathlibExt.GameTheory.ShapleyValue

variable [DecidableEq Player] [Fintype Player]
/--
[image_univ_perm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/ShapleyValue.lean)
-/
@[path]
private lemma image_univ_perm (σ : Equiv.Perm Player) :
  Finset.image (⇑σ) Finset.univ = Finset.univ := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro _
    trivial
  · intro _
    exact ⟨σ.symm x, Equiv.apply_symm_apply σ x⟩

end MathlibExt.GameTheory.ShapleyValue

namespace MathlibExt.GameTheory.ShapleyValue

variable [DecidableEq Player] [Fintype Player]
/--
[shapley_symmetric](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/ShapleyValue.lean)
-/
@[path]
private lemma shapley_symmetric : IsSymmetric
  (shapleyLM : CoopGame Player →ₗ[ℝ] (Player → ℝ)) := by
  intro σ v hinv i
  rw [shapleyLM_apply, shapleyLM_apply, Finset.sum_filter, Finset.sum_filter]
  have hinj : Function.Injective (⇑σ) := Equiv.injective σ
  have hpowerset_image : (Finset.univ : Finset Player).powerset
    = Finset.image (fun T => Finset.image (⇑σ) T)
      (Finset.univ : Finset Player).powerset := by
    have himg : Finset.image (⇑σ) (Finset.univ : Finset Player) = Finset.univ :=
      image_univ_perm σ
    have h := Finset.powerset_image (s := (Finset.univ : Finset Player)) (f := (⇑σ))
    rwa [himg] at h
  have hinjOn : Set.InjOn (fun T => Finset.image (⇑σ) T)
    ↑((Finset.univ : Finset Player).powerset) := by
    apply Set.injOn_of_injective
    exact Finset.image_injective hinj
  conv_lhs => rw [hpowerset_image, Finset.sum_image hinjOn]
  apply Finset.sum_congr rfl
  intro T _
  have hmem : (σ i ∈ Finset.image (⇑σ) T) ↔ (i ∈ T) := by
    constructor
    · intro h
      rw [Finset.mem_image] at h
      obtain ⟨a, haT, haeq⟩ := h
      have heq : a = i := hinj haeq
      subst heq
      exact haT
    · intro h
      rw [Finset.mem_image]
      exact ⟨i, h, rfl⟩
  have hcard : (Finset.image (⇑σ) T).card = T.card :=
    Finset.card_image_of_injective T hinj
  have hmob : mobiusCoeff v (Finset.image (⇑σ) T) = mobiusCoeff v T :=
    mobiusCoeff_perm σ v hinv T
  by_cases hi : i ∈ T
  · have hσmem : σ i ∈ Finset.image (⇑σ) T := hmem.mpr hi
    rw [ite_eq_left hσmem, ite_eq_left hi, hmob, hcard]
  · have hσnmem : σ i ∉ Finset.image (⇑σ) T := fun h => hi (hmem.mp h)
    rw [ite_eq_right hσnmem, ite_eq_right hi]

end MathlibExt.GameTheory.ShapleyValue

/--
[shapley_characterization](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/ShapleyValue.lean)
-/
@[path]
private lemma shapley_characterization_eq
  [DecidableEq Player] [Fintype Player] :
-- imply
  ∃! φ : CoopGame Player →ₗ[ℝ] (Player → ℝ),
    IsEfficient φ ∧ IsSymmetric φ ∧ SatisfiesNullPlayerAxiom φ := by
-- proof
  apply MathlibExt.GameTheory.ShapleyValue.shapley_characterization


-- created on 2026-10-20
-- updated on 2026-10-23

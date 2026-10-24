import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicCombinatorics.code.SubsetSum
open SpernerProperty YoungLattice YoungLattice.Lmn Finset SubsetSum


namespace SubsetSum

/--
[eq_of_le_of_sum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SubsetSum.lean)
-/
@[path]
lemma eq_of_le_of_sum_eq
  {k : ℕ}
  {x y : Fin k → ℝ}
-- given
  (hle : ∀ i, x i ≤ y i)
  (hsum : ∑ i, x i = ∑ i, y i) :
-- imply
  ∀ i, x i = y i := by
-- proof
  by_contra h
  push_neg at h
  obtain ⟨i₀, hi₀⟩ := h
  have hlt : x i₀ < y i₀ := lt_of_le_of_ne (hle i₀) hi₀
  have : ∑ i, x i < ∑ i, y i :=
    Finset.sum_lt_sum (fun i _ => hle i) ⟨i₀, Finset.mem_univ _, hlt⟩
  linarith

end SubsetSum

namespace SubsetSum

/--
[claim_indices_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SubsetSum.lean)
-/
@[path]
lemma claim_indices_eq
  {n k : ℕ}
  {a : Fin n → ℝ}
  {is js : Fin k → Fin n}
-- given
  (ha : StrictMono a)
  (h_le : ∀ r, is r ≤ js r)
  (h_sum : ∑ r, a (is r) = ∑ r, a (js r)) :
-- imply
  ∀ r, is r = js r := by
-- proof
  have ha_le : ∀ r, a (is r) ≤ a (js r) := fun r => ha.monotone (h_le r)
  have ha_eq := eq_of_le_of_sum_eq ha_le h_sum
  intro r
  exact le_antisymm (h_le r) (not_lt.mp (fun h => (ha h).ne (ha_eq r)))

end SubsetSum

namespace SubsetSum

/--
[claim_incomparable_of_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SubsetSum.lean)
-/
@[path]
lemma claim_incomparable_of_distinct
  {n k : ℕ}
  {a : Fin n → ℝ}
  {is js : Fin k → Fin n}
-- given
  (ha : StrictMono a)
  (h_ne : is ≠ js)
  (h_sum : ∑ r, a (is r) = ∑ r, a (js r)) :
-- imply
  ¬(∀ r, is r ≤ js r) := by
-- proof
  intro h_le
  exact h_ne (funext (claim_indices_eq ha h_le h_sum))

end SubsetSum

namespace SubsetSum

/--
[gauss_sum_fin](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SubsetSum.lean)
-/
@[path]
lemma gauss_sum_fin
  {k : ℕ} :
-- imply
  ∑ r : Fin k, (r.val + 1) = k * (k + 1) / 2 := by
-- proof
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    obtain ⟨q1, hq1⟩ := Even.two_dvd (Nat.even_mul_succ_self n)
    obtain ⟨q2, hq2⟩ := Even.two_dvd (Nat.even_mul_succ_self (n + 1))
    rw [hq1, show (n + 1) * (n + 1 + 1) = (n + 1) * (n + 2) from by ring, hq2]
    simp only [Nat.mul_div_cancel_left _ (by omega : 0 < 2)]; nlinarith

end SubsetSum

namespace SubsetSum

/--
[embed_strictMono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SubsetSum.lean)
-/
@[path]
lemma embed_strictMono
  {k m : ℕ}
  {f : Fin k → Fin (m + 1)}
-- given
  (hf : Antitone f) :
-- imply
  StrictMono (fun r : Fin k => (f (Fin.rev r)).val + r.val + 1) := by
-- proof
  intro a b hab
  simp only
  have : (f (Fin.rev a)).val ≤ (f (Fin.rev b)).val := hf (Fin.rev_le_rev.mpr (le_of_lt hab))
  omega

end SubsetSum

namespace SubsetSum

/--
[embed_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SubsetSum.lean)
-/
@[path]
lemma embed_sum
  {k m : ℕ}
  {f : Fin k → Fin (m + 1)} :
-- imply
  ∑ r : Fin k, ((f (Fin.rev r)).val + r.val + 1) = (∑ i : Fin k, (f i).val) + k * (k + 1) / 2 := by
-- proof
  conv_lhs =>
    rw [show (fun r : Fin k => (f (Fin.rev r)).val + r.val + 1) =
      (fun r => (f (Fin.rev r)).val + (r.val + 1)) from by ext; omega]
  rw [Finset.sum_add_distrib]
  congr 1
  · exact Fintype.sum_equiv Fin.revPerm _ _ (fun r => by simp [Fin.revPerm])
  · exact gauss_sum_fin k

end SubsetSum

namespace SubsetSum

/--
[lambdaMapForward_card](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SubsetSum.lean)
-/
@[path]
lemma lambdaMapForward_card
  {k m : ℕ}
  {p : Lmn k m} :
-- imply
  (lambdaMapForward k m p).card = k := by
-- proof
  simp [lambdaMapForward, Finset.card_image_of_injective _ (embed_strictMono p.property).injective]

end SubsetSum

namespace SubsetSum

/--
[lambdaMapForward_subset_iccNat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SubsetSum.lean)
-/
@[path]
lemma lambdaMapForward_subset_iccNat
  {k m : ℕ}
  {p : Lmn k m} :
-- imply
  lambdaMapForward k m p ⊆ iccNat (k + m) := by
-- proof
  intro x hx
  simp only [lambdaMapForward, Finset.mem_image, Finset.mem_univ, true_and] at hx
  obtain ⟨r, rfl⟩ := hx
  simp only [iccNat, Finset.mem_Icc]
  constructor
  · omega
  · have : (p.val (Fin.rev r)).val ≤ m := Fin.is_le _
    have : r.val ≤ k - 1 := by omega
    omega

end SubsetSum

namespace SubsetSum

/--
[lambdaMapForward_mem_powersetCard](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SubsetSum.lean)
-/
@[path]
lemma lambdaMapForward_mem_powersetCard
  {k m : ℕ}
  {p : Lmn k m} :
-- imply
  lambdaMapForward k m p ∈ powersetCard k (iccNat (k + m)) := by
-- proof
  rw [Finset.mem_powersetCard]
  exact ⟨lambdaMapForward_subset_iccNat k m p, lambdaMapForward_card k m p⟩

end SubsetSum

namespace SubsetSum

/--
[lambdaMapForward_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SubsetSum.lean)
-/
@[path]
lemma lambdaMapForward_sum
  {k m : ℕ}
  {p : Lmn k m} :
-- imply
  (lambdaMapForward k m p).sum id = sumParts p + k * (k + 1) / 2 := by
-- proof
  simp only [lambdaMapForward]
  rw [Finset.sum_image (fun x _ y _ h => (embed_strictMono p.property).injective h)]
  simp only [id]
  exact embed_sum p.val

end SubsetSum

namespace SubsetSum

/--
[strictMono_image_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SubsetSum.lean)
-/
@[path]
lemma strictMono_image_eq
  {k : ℕ}
  {f g : Fin k → ℕ}
-- given
  (hf : StrictMono f)
  (hg : StrictMono g)
  (h : (Finset.univ : Finset (Fin k)).image f = Finset.univ.image g) :
-- imply
  f = g := by
-- proof
  have hcard : (Finset.univ.image f).card = k := by
    rw [Finset.card_image_of_injective _ hf.injective]; simp
  have hf_mem : ∀ x, f x ∈ Finset.univ.image f :=
    fun x => Finset.mem_image_of_mem f (Finset.mem_univ x)
  have hg_mem : ∀ x, g x ∈ Finset.univ.image f :=
    fun x => h ▸ Finset.mem_image_of_mem g (Finset.mem_univ x)
  have hf_eq := Finset.orderEmbOfFin_unique hcard hf_mem hf
  have hg_eq := Finset.orderEmbOfFin_unique hcard hg_mem hg
  calc f = ⇑((Finset.univ.image f).orderEmbOfFin hcard) := hf_eq
    _ = g := hg_eq.symm

end SubsetSum

namespace SubsetSum

/--
[lambdaMapForward_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SubsetSum.lean)
-/
@[path]
lemma lambdaMapForward_injective
  {k m : ℕ} :
-- imply
  Function.Injective (lambdaMapForward k m) := by
-- proof
  intro p q hpq
  let fp : Fin k → ℕ := fun r => (p.val (Fin.rev r)).val + r.val + 1
  let fq : Fin k → ℕ := fun r => (q.val (Fin.rev r)).val + r.val + 1
  have h_eq : Finset.univ.image fp = Finset.univ.image fq := hpq
  have hfp_sm := embed_strictMono p.property
  have hfq_sm := embed_strictMono q.property
  have h_fun := strictMono_image_eq hfp_sm hfq_sm h_eq
  ext i
  have := congr_fun h_fun (Fin.rev i)
  simp only [Fin.rev_rev] at this
  omega

end SubsetSum

namespace SubsetSum

/--
[subsetSumCountNat_eq_rankCount](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SubsetSum.lean)
-/
@[path]
lemma subsetSumCountNat_eq_rankCount
  {k n α : ℕ}
-- given
  (hk : k ≤ n)
  (hα : k * (k + 1) / 2 ≤ α) :
-- imply
  subsetSumCountNat k n α = rankCount (α := Lmn k (n - k)) (α - k * (k + 1) / 2) := by
-- proof
  simp only [subsetSumCountNat, rankCount]
  have hn_eq : k + (n - k) = n := by omega
  symm
  apply Finset.card_nbij (fun p => lambdaMapForward k (n - k) p)
  ·
    intro p hp
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hp ⊢
    refine ⟨?_, ?_⟩
    · have h := lambdaMapForward_mem_powersetCard k (n - k) p; rwa [hn_eq] at h
    · rw [lambdaMapForward_sum]; rw [Lmn.grade_eq] at hp; omega
  ·
    intro p _ q _ hpq; exact lambdaMapForward_injective k (n - k) hpq
  ·
    intro T hT
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and,
      Set.mem_image] at hT ⊢
    obtain ⟨hTmem, hTsum⟩ := hT
    have hcard : T.card = k := (Finset.mem_powersetCard.mp hTmem).2
    have hTsub : T ⊆ iccNat n := (Finset.mem_powersetCard.mp hTmem).1
    set s := T.orderEmbOfFin hcard with hs_def
    have hs_mono : StrictMono s := s.strictMono
    have hs_mem : ∀ r, (s r : ℕ) ∈ T := fun r => Finset.orderEmbOfFin_mem T hcard r
    have hs_ge : ∀ r : Fin k, r.val + 1 ≤ (s r : ℕ) := by
      intro r
      have hk_pos : 0 < k := r.pos
      have hs0 : 1 ≤ (s ⟨0, hk_pos⟩ : ℕ) := by
        have := hTsub (hs_mem ⟨0, hk_pos⟩)
        simp only [iccNat, Finset.mem_Icc] at this; exact this.1
      by_cases hr0 : r.val = 0
      · have : r = ⟨0, hk_pos⟩ := Fin.ext (by omega); rw [this]; omega
      · have h0r : (⟨0, hk_pos⟩ : Fin k) < r := Fin.mk_lt_mk.mpr (by omega)
        have := strictMono_fin_add_le hs_mono ⟨0, hk_pos⟩ r (le_of_lt h0r)
        simp at this; omega
    have hs_le_n : ∀ r : Fin k, (s r : ℕ) ≤ n := by
      intro r
      have := hTsub (hs_mem r)
      simp only [iccNat, Finset.mem_Icc] at this; exact this.2
    have hs_bound : ∀ r : Fin k, (s r : ℕ) - r.val - 1 ≤ n - k := by
      intro r
      have hk_pos : 0 < k := r.pos
      have hlast := hs_le_n ⟨k - 1, by omega⟩
      by_cases hrk : r.val = k - 1
      · have : r = ⟨k - 1, by omega⟩ := Fin.ext (by omega); rw [this]; omega
      · have hlt : r < ⟨k - 1, by omega⟩ := Fin.mk_lt_mk.mpr (by omega)
        have := strictMono_fin_add_le hs_mono r ⟨k - 1, by omega⟩ (le_of_lt hlt)
        simp at this; omega
    let p : Lmn k (n - k) :=
      ⟨fun i => ⟨(s (Fin.rev i) : ℕ) - (Fin.rev i).val - 1, by
        have := hs_bound (Fin.rev i); omega⟩,
      fun a b hab => by
        simp only [Fin.le_def]
        have hrev := Fin.rev_le_rev.mpr hab
        have h := strictMono_fin_add_le hs_mono (Fin.rev b) (Fin.rev a) hrev
        have := hs_ge (Fin.rev a)
        have := hs_ge (Fin.rev b)
        omega⟩
    refine ⟨p, ?_, ?_⟩
    ·
      rw [Lmn.grade_eq]
      simp only [Lmn.sumParts, p]
      have h_reindex : ∑ x : Fin k, ((s (Fin.rev x) : ℕ) - (Fin.rev x).val - 1) =
        ∑ x : Fin k, ((s x : ℕ) - x.val - 1) :=
        Fintype.sum_equiv Fin.revPerm (fun x => (s (Fin.rev x) : ℕ) - (Fin.rev x).val - 1)
          (fun x => (s x : ℕ) - x.val - 1)
          (fun r => by simp [Fin.revPerm])
      rw [h_reindex]
      have h_pw : ∀ r : Fin k, (s r : ℕ) - r.val - 1 = (s r : ℕ) - (r.val + 1) := by
        intro r; omega
      simp_rw [h_pw]
      have h_add : ∀ r : Fin k, (s r : ℕ) - (r.val + 1) + (r.val + 1) = (s r : ℕ) := by
        intro r; have := hs_ge r; omega
      have h_split := Finset.sum_add_distrib (f := fun r : Fin k => (s r : ℕ) - (r.val + 1))
        (g := fun r => r.val + 1) (s := Finset.univ)
      rw [show ∑ r : Fin k, ((s r : ℕ) - (r.val + 1) + (r.val + 1)) = ∑ r : Fin k, (s r : ℕ)
        from Finset.sum_congr rfl (fun r _ => h_add r)] at h_split
      have h_sum_s : ∑ r : Fin k, (s r : ℕ) = T.sum id := by
        rw [show T.sum id = ∑ x ∈ T, id x from rfl]
        rw [show id = (fun x : ℕ => x) from rfl]
        rw [← Finset.sum_image (f := fun x : ℕ => x)
          (g := fun r : Fin k => (s r : ℕ))
          (fun a _ b _ h => s.injective (by exact_mod_cast h : s a = s b))]
        congr 1
        ext x; simp only [Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨fun ⟨r, hr⟩ => hr ▸ hs_mem r, fun hx => by
          have : x ∈ Set.range s := by rw [Finset.range_orderEmbOfFin T hcard]; exact hx
          obtain ⟨r, rfl⟩ := this; exact ⟨r, rfl⟩⟩
      rw [h_sum_s, hTsum, gauss_sum_fin] at h_split
      omega
    ·
      ext x
      simp only [lambdaMapForward, Finset.mem_image, Finset.mem_univ, true_and, p, Fin.rev_rev]
      constructor
      · rintro ⟨r, hr⟩
        have hge := hs_ge r
        have : (s r : ℕ) - r.val - 1 + r.val + 1 = (s r : ℕ) := by omega
        rw [this] at hr; rw [← hr]; exact hs_mem r
      · intro hx
        have hrange := Finset.range_orderEmbOfFin T hcard
        have : x ∈ Set.range s := by rw [hrange]; exact hx
        obtain ⟨r, rfl⟩ := this
        exact ⟨r, by have := hs_ge r; omega⟩

end SubsetSum

namespace SubsetSum

/--
[arith_identity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SubsetSum.lean)
-/
@[path]
lemma arith_identity
  {k n : ℕ}
-- given
  (hk : k ≤ n) :
-- imply
  k * (n + 1) / 2 - k * (k + 1) / 2 = k * (n - k) / 2 := by
-- proof
  have h_sum : k * (n + 1) = k * (k + 1) + k * (n - k) := by
    rw [← Nat.mul_add]; congr 1; omega
  have h_dvd : 2 ∣ k * (k + 1) := Even.two_dvd (Nat.even_mul_succ_self k)
  rw [h_sum, Nat.add_div_of_dvd_right h_dvd]
  omega

end SubsetSum

namespace SubsetSum

/--
[maxRankCount_Lmn_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SubsetSum.lean)
-/
@[path]
lemma maxRankCount_Lmn_eq
  {k n : ℕ}
-- given
  (hk : k ≤ n) :
-- imply
  maxRankCount (α := Lmn k (n - k)) = subsetSumCountNat k n (k * (n + 1) / 2) := by
-- proof
  have h_mid := GraphIsoPoset.maxRankCount_eq_middle_of_symmetric_unimodal
    (Lmn_isRankSymmetric k (n - k)) (Lmn_isRankUnimodal k (n - k))
  have h_rank : GradedPoset.rank (α := Lmn k (n - k)) = k * (n - k) := rfl
  rw [h_rank] at h_mid
  have hα : k * (k + 1) / 2 ≤ k * (n + 1) / 2 :=
    Nat.div_le_div_right (Nat.mul_le_mul_left k (by omega))
  have h_eq34 := subsetSumCountNat_eq_rankCount k n (k * (n + 1) / 2) hk hα
  have h_arith := arith_identity k n hk
  rwa [h_mid, ← h_arith]

end SubsetSum

namespace SubsetSum

/--
[orderEmb_idxFun_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SubsetSum.lean)
-/
@[path]
lemma orderEmb_idxFun_eq
  {S : Finset ℝ}
  {n : ℕ}
  {T : Finset ℝ}
  {k : ℕ}
  {r : Fin k}
-- given
  (hScard : S.card = n)
  (hTcard : T.card = k)
  (hTsub : T ⊆ S) :
-- imply
  (S.orderEmbOfFin hScard (idxFun S n hScard T k hTcard hTsub r) : ℝ) = T.orderEmbOfFin hTcard r := by
-- proof
  simp only [idxFun]
  rw [← Finset.coe_orderIsoOfFin_apply]
  simp only [OrderIso.apply_symm_apply]

end SubsetSum

namespace SubsetSum

/--
[toLmn_le_implies_idx_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SubsetSum.lean)
-/
@[path]
lemma toLmn_le_implies_idx_le
  {S : Finset ℝ}
  {n : ℕ}
  {T : Finset ℝ}
  {k : ℕ}
  {U : Finset ℝ}
  {r : Fin k}
-- given
  (hScard : S.card = n)
  (hTcard : T.card = k)
  (hTsub : T ⊆ S)
  (hUcard : U.card = k)
  (hUsub : U ⊆ S)
  (hkn : k ≤ n)
  (h : toLmn S n hScard T k hTcard hTsub hkn ≤ toLmn S n hScard U k hUcard hUsub hkn) :
-- imply
  (idxFun S n hScard T k hTcard hTsub r).val ≤ (idxFun S n hScard U k hUcard hUsub r).val := by
-- proof
  have h_pw : ∀ i : Fin k,
    (idxVal S n hScard T k hTcard hTsub (Fin.rev i) - (Fin.rev i).val) ≤
    (idxVal S n hScard U k hUcard hUsub (Fin.rev i) - (Fin.rev i).val) := by
    intro i
    have hi := h i
    simp only [toLmn, Fin.le_def] at hi
    exact hi
  specialize h_pw (Fin.rev r)
  simp only [Fin.rev_rev] at h_pw
  have hT_ge := idxVal_ge S n hScard T k hTcard hTsub r
  have hU_ge := idxVal_ge S n hScard U k hUcard hUsub r
  simp only [idxVal] at *
  omega

end SubsetSum

namespace SubsetSum

/--
[sum_orderEmb](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SubsetSum.lean)
-/
@[path]
lemma sum_orderEmb
  {S : Finset ℝ}
  {n : ℕ}
  {T : Finset ℝ}
  {k : ℕ}
-- given
  (hScard : S.card = n)
  (hTcard : T.card = k)
  (hTsub : T ⊆ S) :
-- imply
  ∑ r : Fin k, (S.orderEmbOfFin hScard (idxFun S n hScard T k hTcard hTsub r) : ℝ) = T.sum id := by
-- proof
  have h_eq : ∀ r : Fin k,
    (S.orderEmbOfFin hScard (idxFun S n hScard T k hTcard hTsub r) : ℝ) =
    (T.orderEmbOfFin hTcard r : ℝ) :=
    fun r => orderEmb_idxFun_eq S n hScard T k hTcard hTsub r
  simp_rw [h_eq]
  have hT_eq : T = Finset.univ.image (fun r => (T.orderEmbOfFin hTcard r : ℝ)) := by
    ext x; simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun hx => by
      have : x ∈ Set.range (T.orderEmbOfFin hTcard) := by
        rw [Finset.range_orderEmbOfFin T hTcard]; exact hx
      obtain ⟨r, rfl⟩ := this; exact ⟨r, rfl⟩,
    fun ⟨r, hr⟩ => hr ▸ Finset.orderEmbOfFin_mem T hTcard r⟩
  conv_rhs => rw [hT_eq]
  rw [Finset.sum_image (fun a _ b _ hab => (T.orderEmbOfFin hTcard).injective hab)]
  simp

end SubsetSum

namespace SubsetSum

/--
[subsetSumCount_le_maxRankCount](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SubsetSum.lean)
-/
@[path]
lemma subsetSumCount_le_maxRankCount
  {n k : ℕ}
  {S : Finset ℝ}
  {α : ℝ}
-- given
  (hk : 0 < k)
  (hScard : S.card = n)
  (hSpos : ∀ x ∈ S, (0 : ℝ) < x)
  (hα : 0 < α) :
-- imply
  subsetSumCount k S α ≤ maxRankCount (α := Lmn k (n - k)) := by
-- proof
  by_cases hkn : k ≤ n
  ·
    set F := (powersetCard k S).filter (fun T => T.sum id = α) with hF_def
    set eS := S.orderEmbOfFin hScard with heS_def
    have heS_sm : StrictMono eS := eS.strictMono
    let φ : (T : Finset ℝ) → T ∈ F → Lmn k (n - k) := fun T hT =>
      toLmn S n hScard T k
        (by simp only [hF_def, Finset.mem_filter, Finset.mem_powersetCard] at hT; exact hT.1.2)
        (by simp only [hF_def, Finset.mem_filter, Finset.mem_powersetCard] at hT; exact hT.1.1)
        hkn
    have h_antichain : ∀ (T : Finset ℝ) (hT : T ∈ F) (U : Finset ℝ) (hU : U ∈ F),
      T ≠ U → ¬(toLmn S n hScard T k
        (by simp only [hF_def, Finset.mem_filter, Finset.mem_powersetCard] at hT; exact hT.1.2)
        (by simp only [hF_def, Finset.mem_filter, Finset.mem_powersetCard] at hT; exact hT.1.1)
        hkn ≤
      toLmn S n hScard U k
        (by simp only [hF_def, Finset.mem_filter, Finset.mem_powersetCard] at hU; exact hU.1.2)
        (by simp only [hF_def, Finset.mem_filter, Finset.mem_powersetCard] at hU; exact hU.1.1)
        hkn) := by
      intro T hT U hU hTU hle
      have hTcard : T.card = k := by
        simp only [hF_def, Finset.mem_filter, Finset.mem_powersetCard] at hT; exact hT.1.2
      have hTsub : T ⊆ S := by
        simp only [hF_def, Finset.mem_filter, Finset.mem_powersetCard] at hT; exact hT.1.1
      have hUcard : U.card = k := by
        simp only [hF_def, Finset.mem_filter, Finset.mem_powersetCard] at hU; exact hU.1.2
      have hUsub : U ⊆ S := by
        simp only [hF_def, Finset.mem_filter, Finset.mem_powersetCard] at hU; exact hU.1.1
      have hTsum : T.sum id = α := by
        simp only [hF_def, Finset.mem_filter] at hT; exact hT.2
      have hUsum : U.sum id = α := by
        simp only [hF_def, Finset.mem_filter] at hU; exact hU.2
      have h_idx_le : ∀ r : Fin k,
        (idxFun S n hScard T k hTcard hTsub r).val ≤
        (idxFun S n hScard U k hUcard hUsub r).val :=
        toLmn_le_implies_idx_le S n hScard T k hTcard hTsub U hUcard hUsub hkn hle
      let isT := idxFun S n hScard T k hTcard hTsub
      let isU := idxFun S n hScard U k hUcard hUsub
      have h_le_fin : ∀ r, isT r ≤ isU r := fun r => h_idx_le r
      have h_sum_T := sum_orderEmb S n hScard T k hTcard hTsub
      have h_sum_U := sum_orderEmb S n hScard U k hUcard hUsub
      have h_sum_eq : ∑ r : Fin k, (eS (isT r) : ℝ) = ∑ r : Fin k, (eS (isU r) : ℝ) := by
        rw [h_sum_T, h_sum_U, hTsum, hUsum]
      have h_ne_idx : isT ≠ isU := by
        intro heq
        have : ∀ r : Fin k, (T.orderEmbOfFin hTcard r : ℝ) = U.orderEmbOfFin hUcard r := by
          intro r
          have h_idx_eq := congr_fun heq r
          rw [← orderEmb_idxFun_eq S n hScard T k hTcard hTsub r,
            ← orderEmb_idxFun_eq S n hScard U k hUcard hUsub r]
          congr 1
        have hT_eq_U : T = U := by
          have hT_range : T = Finset.univ.image (fun r => (T.orderEmbOfFin hTcard r : ℝ)) := by
            ext x; simp only [Finset.mem_image, Finset.mem_univ, true_and]
            exact ⟨fun hx => by
              have : x ∈ Set.range (T.orderEmbOfFin hTcard) := by
                rw [Finset.range_orderEmbOfFin T hTcard]; exact hx
              obtain ⟨r, rfl⟩ := this; exact ⟨r, rfl⟩,
            fun ⟨r, hr⟩ => hr ▸ Finset.orderEmbOfFin_mem T hTcard r⟩
          have hU_range : U = Finset.univ.image (fun r => (U.orderEmbOfFin hUcard r : ℝ)) := by
            ext x; simp only [Finset.mem_image, Finset.mem_univ, true_and]
            exact ⟨fun hx => by
              have : x ∈ Set.range (U.orderEmbOfFin hUcard) := by
                rw [Finset.range_orderEmbOfFin U hUcard]; exact hx
              obtain ⟨r, rfl⟩ := this; exact ⟨r, rfl⟩,
            fun ⟨r, hr⟩ => hr ▸ Finset.orderEmbOfFin_mem U hUcard r⟩
          rw [hT_range, hU_range]
          congr 1; ext r; exact this r
        exact hTU hT_eq_U
      exact claim_incomparable_of_distinct heS_sm h_ne_idx h_sum_eq h_le_fin
    set A := F.attach.image (fun ⟨T, hT⟩ => φ T hT) with hA_def
    have hA_card : F.card = A.card := by
      rw [hA_def]
      rw [Finset.card_image_of_injective _ (fun ⟨a, ha⟩ ⟨b, hb⟩ h => by
        simp only [Subtype.mk.injEq]
        by_contra hab
        have hle : toLmn S n hScard a k
          (by simp only [hF_def, Finset.mem_filter, Finset.mem_powersetCard] at ha; exact ha.1.2)
          (by simp only [hF_def, Finset.mem_filter, Finset.mem_powersetCard] at ha; exact ha.1.1)
          hkn ≤
          toLmn S n hScard b k
          (by simp only [hF_def, Finset.mem_filter, Finset.mem_powersetCard] at hb; exact hb.1.2)
          (by simp only [hF_def, Finset.mem_filter, Finset.mem_powersetCard] at hb; exact hb.1.1)
          hkn := le_of_eq h
        exact h_antichain a ha b hb hab hle)]
      exact Finset.card_attach.symm
    have hA_anti : IsAntichain (· ≤ ·) (A : Set (Lmn k (n - k))) := by
      intro p hp q hq hpq
      rw [hA_def, Finset.coe_image] at hp hq
      obtain ⟨⟨T, hT⟩, _, rfl⟩ := hp
      obtain ⟨⟨U, hU⟩, _, rfl⟩ := hq
      have hTU : T ≠ U := by
        intro heq; subst heq
        exact hpq rfl
      exact h_antichain T hT U hU hTU
    have hsp := YoungLattice.Lmn.hasSpernerProperty k (n - k)
    calc subsetSumCount k S α = F.card := rfl
      _ = A.card := hA_card
      _ ≤ maxRankCount (α := Lmn k (n - k)) := hsp A hA_anti
  ·
    push Not at hkn
    have : powersetCard k S = ∅ := by rw [Finset.powersetCard_eq_empty, hScard]; omega
    simp [subsetSumCount, this]

end SubsetSum

namespace SubsetSum

/--
[subset_sum_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SubsetSum.lean)
-/
@[path]
lemma subset_sum_bound
  {n k : ℕ}
  {S : Finset ℝ}
  {α : ℝ}
-- given
  (hk : 0 < k)
  (hScard : S.card = n)
  (hSpos : ∀ x ∈ S, (0 : ℝ) < x)
  (hα : 0 < α) :
-- imply
  subsetSumCount k S α ≤ subsetSumCountNat k n (k * (n + 1) / 2) := by
-- proof
  by_cases hkn : k ≤ n
  · calc subsetSumCount k S α
    ≤ maxRankCount (α := Lmn k (n - k)) :=
      subsetSumCount_le_maxRankCount n k hk S hScard hSpos α hα
    _ = subsetSumCountNat k n (k * (n + 1) / 2) :=
      maxRankCount_Lmn_eq k n hkn
  ·
    push_neg at hkn
    have : powersetCard k S = ∅ := by
      rw [Finset.powersetCard_eq_empty, hScard]
      omega
    simp [subsetSumCount, this]

end SubsetSum

/--
[strictMono_fin_add_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SubsetSum.lean)
-/
@[path]
private lemma strictMono_fin_add_le_eq
  {k : ℕ}
  {s : Fin k → ℕ}
  {a b : Fin k}
-- given
  (hs : StrictMono s)
  (hab : a ≤ b) :
-- imply
  s a + (b.val - a.val) ≤ s b := by
-- proof
  apply SubsetSum.strictMono_fin_add_le hs a b hab

/--
[idxFun_strictMono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SubsetSum.lean)
-/
@[path]
private lemma idxFun_strictMono_eq
  {S : Finset ℝ}
  {n : ℕ}
  {T : Finset ℝ}
  {k : ℕ}
-- given
  (hScard : S.card = n)
  (hTcard : T.card = k)
  (hTsub : T ⊆ S) :
-- imply
  StrictMono (idxFun S n hScard T k hTcard hTsub) := by
-- proof
  apply SubsetSum.idxFun_strictMono S n hScard T k hTcard hTsub

/--
[idxVal_ge](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SubsetSum.lean)
-/
@[path]
private lemma idxVal_ge_eq
  {S : Finset ℝ}
  {n : ℕ}
  {T : Finset ℝ}
  {k : ℕ}
  {r : Fin k}
-- given
  (hScard : S.card = n)
  (hTcard : T.card = k)
  (hTsub : T ⊆ S) :
-- imply
  r.val ≤ idxVal S n hScard T k hTcard hTsub r := by
-- proof
  apply SubsetSum.idxVal_ge S n hScard T k hTcard hTsub r

/--
[idxVal_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SubsetSum.lean)
-/
@[path]
private lemma idxVal_bound_eq
  {S : Finset ℝ}
  {n : ℕ}
  {T : Finset ℝ}
  {k : ℕ}
  {r : Fin k}
-- given
  (hScard : S.card = n)
  (hTcard : T.card = k)
  (hTsub : T ⊆ S)
  (hkn : k ≤ n) :
-- imply
  idxVal S n hScard T k hTcard hTsub r - r.val ≤ n - k := by
-- proof
  apply SubsetSum.idxVal_bound S n hScard T k hTcard hTsub hkn r


-- created on 2026-10-23

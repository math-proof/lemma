import Mathlib
import Initialize.Tactic.Attr.Basic


namespace MetaMathlibExt

/--
[ballot_poly](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/BertrandBallot.lean)
-/
@[path]
private lemma ballot_poly {p q : ℕ} (hq : 1 ≤ q) (hlt : q < p) :
  (p - 1 - q) * p + (p - (q - 1)) * q = (p - q) * (p + q - 1) := by
  obtain ⟨d, rfl⟩ : ∃ d, p = q + (d + 1) := ⟨p - q - 1, by omega⟩
  have e1 : q + (d + 1) - 1 - q = d := by omega
  have e2 : q + (d + 1) - (q - 1) = d + 2 := by omega
  have e3 : q + (d + 1) - q = d + 1 := by omega
  have e4 : q + (d + 1) + q - 1 = 2 * q + d := by omega
  rw [e1, e2, e3, e4]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ballot_arith](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/BertrandBallot.lean)
-/
@[path]
private lemma ballot_arith {p q F1 F2 : ℕ} (hq : 1 ≤ q) (hlt : q < p) :
  let S := p + q - 1
  let C1 := S.choose q
  let _C2 := S.choose (q - 1)
  let C := (p + q).choose q
  F1 * S = (p - 1 - q) * C1 →
  F2 * S = (p - (q - 1)) * (S.choose (q - 1)) →
  (F1 + F2) * (p + q) = (p - q) * C := by
  intro S C1 _C2 C h1 h2
  have hpq : p + q = S + 1 := by omega
  have hqsucc : (q - 1).succ = q := by omega
  have hSsucc : S.succ = S + 1 := rfl
  have hP : C = S.choose (q - 1) + C1 := by
    simp only [C, C1]
    conv_lhs => rw [hpq]
    have h := Nat.choose_succ_succ S (q - 1)
    rw [hSsucc, hqsucc] at h
    have h2 : S.choose (q - 1).succ = S.choose q := by rw [hqsucc]
    omega
  have hR1 : C1 * (p + q) = C * p := by
    simp only [C, C1]
    have h := Nat.choose_mul_succ_eq S q
    rw [← hpq] at h
    have hPq : p + q - q = p := by omega
    rwa [hPq] at h
  have hR2 : S.choose (q - 1) * (p + q) = C * q := by
    simp only [C]
    have h := Nat.add_one_mul_choose_eq S (q - 1)
    have hq' : q - 1 + 1 = q := by omega
    rw [hq'] at h
    have hpq2 : S + 1 = p + q := by omega
    rw [hpq2] at h
    linear_combination h
  have hpoly := ballot_poly hq hlt
  have hC2 : _C2 = S.choose (q - 1) := rfl
  have hcomb : ((F1 + F2) * (p + q)) * S = ((p - q) * C) * S := by
    have e1 : (F1 + F2) * (p + q) * S = (F1 * S) * (p + q) + (F2 * S) * (p + q) := by ring
    rw [e1, h1, h2]
    have e2 : (p - 1 - q) * C1 * (p + q) + (p - (q - 1)) * S.choose (q - 1) * (p + q)
      = (p - 1 - q) * (C * p) + (p - (q - 1)) * (C * q) := by
      rw [← hR1, ← hR2]; ring
    rw [e2]
    have e3 : (p - 1 - q) * (C * p) + (p - (q - 1)) * (C * q)
      = C * ((p - 1 - q) * p + (p - (q - 1)) * q) := by ring
    rw [e3, hpoly]
    ring
  exact Nat.mul_right_cancel (by omega : 0 < S) hcomb

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ballot_false_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/BertrandBallot.lean)
-/
@[path]
private lemma ballot_false_card {n p : ℕ} {σ : Fin n → Bool}
  (hcount : (Finset.univ.filter (fun i : Fin n => σ i = true)).card = p) :
  (Finset.univ.filter (fun i : Fin n => σ i = false)).card = n - p := by
  have hadd := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (fun i => σ i = true)
  simp only [Finset.card_univ, Fintype.card_fin] at hadd
  rw [hcount] at hadd
  have heq : (Finset.univ.filter (fun i : Fin n => ¬ σ i = true))
    = Finset.univ.filter (fun i : Fin n => σ i = false) := by
    apply Finset.filter_congr
    intro i _
    simp
  rw [heq] at hadd
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ballot_eq_zero_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/BertrandBallot.lean)
-/
@[path]
private lemma ballot_eq_zero_of_le {p q : ℕ} (hle : p ≤ q) (hpos : 0 < p + q) :
  (Finset.univ.filter (fun σ : Fin (p + q) → Bool =>
    (Finset.univ.filter (fun i : Fin (p + q) => σ i = true)).card = p ∧
    ∀ k : Fin (p + q),
      (Finset.univ.filter (fun i : Fin (p + q) => i ≤ k ∧ σ i = true)).card >
      (Finset.univ.filter (fun i : Fin (p + q) => i ≤ k ∧ σ i = false)).card)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro σ hσ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
  obtain ⟨hcount, hballot⟩ := hσ
  have hne : (Finset.univ : Finset (Fin (p + q))).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, hpos⟩⟩
  set kmax := Finset.univ.max' hne with hkmax
  have hle_max : ∀ i : Fin (p + q), i ≤ kmax :=
    fun i => Finset.le_max' _ _ (Finset.mem_univ i)
  have hT : (Finset.univ.filter (fun i : Fin (p + q) => i ≤ kmax ∧ σ i = true)).card = p := by
    have hfilter : Finset.univ.filter (fun i : Fin (p + q) => i ≤ kmax ∧ σ i = true)
      = Finset.univ.filter (fun i : Fin (p + q) => σ i = true) := by
      apply Finset.filter_congr
      intro i _
      simp [hle_max i]
    rwa [hfilter]
  have hF : (Finset.univ.filter (fun i : Fin (p + q) => i ≤ kmax ∧ σ i = false)).card = q := by
    have hfilter : Finset.univ.filter (fun i : Fin (p + q) => i ≤ kmax ∧ σ i = false)
      = Finset.univ.filter (fun i : Fin (p + q) => σ i = false) := by
      apply Finset.filter_congr
      intro i _
      simp [hle_max i]
    rw [hfilter]
    have hcard := ballot_false_card (n := p + q) (p := p) (σ := σ) hcount
    have hnp : p + q - p = q := by omega
    rwa [hnp] at hcard
  have hlt := hballot kmax
  rw [hT, hF] at hlt
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ballot_one_of_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/BertrandBallot.lean)
-/
@[path]
private lemma ballot_one_of_zero {p : ℕ} (_hp : 0 < p) :
  (Finset.univ.filter (fun σ : Fin p → Bool =>
    (Finset.univ.filter (fun i : Fin p => σ i = true)).card = p ∧
    ∀ k : Fin p,
      (Finset.univ.filter (fun i : Fin p => i ≤ k ∧ σ i = true)).card >
      (Finset.univ.filter (fun i : Fin p => i ≤ k ∧ σ i = false)).card)).card = 1 := by
  have hmem : ∀ σ : Fin p → Bool, σ ∈ Finset.univ.filter (fun σ : Fin p → Bool =>
    (Finset.univ.filter (fun i : Fin p => σ i = true)).card = p ∧
    ∀ k : Fin p,
      (Finset.univ.filter (fun i : Fin p => i ≤ k ∧ σ i = true)).card >
      (Finset.univ.filter (fun i : Fin p => i ≤ k ∧ σ i = false)).card) ↔ σ = fun _ => true := by
    intro σ
    constructor
    · intro hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
      obtain ⟨hcount, _⟩ := hσ
      have hF := ballot_false_card (n := p) (p := p) (σ := σ) hcount
      rw [Nat.sub_self] at hF
      have hempty := Finset.card_eq_zero.mp hF
      have hall : ∀ i : Fin p, σ i = true := by
        intro i
        by_contra hi
        have hfalse : σ i = false := by
          cases h : σ i <;> simp_all
        have hmemF : i ∈ Finset.univ.filter (fun j : Fin p => σ j = false) := by
          simp [hfalse]
        rw [hempty] at hmemF
        simp at hmemF
      funext i
      simp [hall i]
    · intro hσ
      subst hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · simp [Finset.card_univ, Fintype.card_fin]
      · intro k
        have hT : (Finset.univ.filter (fun i : Fin p => i ≤ k ∧ True)) = Finset.Iic k := by
          ext i
          simp [Finset.mem_Iic]
        have hF0 : (Finset.univ.filter (fun i : Fin p => i ≤ k ∧ (true : Bool) = false)) = ∅ := by
          ext i
          simp
        rw [hT, hF0, Finset.card_empty, Fin.card_Iic]
        omega
  have hset : Finset.univ.filter (fun σ : Fin p → Bool =>
    (Finset.univ.filter (fun i : Fin p => σ i = true)).card = p ∧
    ∀ k : Fin p,
      (Finset.univ.filter (fun i : Fin p => i ≤ k ∧ σ i = true)).card >
      (Finset.univ.filter (fun i : Fin p => i ≤ k ∧ σ i = false)).card) = {fun _ => true} := by
    apply Finset.ext
    intro σ
    simp [hmem σ]
  rw [hset, Finset.card_singleton]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[snoc_iic_true](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/BertrandBallot.lean)
-/
@[path]
private lemma snoc_iic_true {m : ℕ} (τ : Fin m → Bool) (b : Bool) (j : Fin m) :
  Finset.image Fin.castSucc (Finset.univ.filter (fun i : Fin m => i ≤ j ∧ τ i = true))
  = Finset.univ.filter (fun i : Fin (m + 1) =>
    i ≤ j.castSucc ∧ Fin.snoc (α := fun _ => Bool) τ b i = true) := by
  apply Finset.ext
  intro i
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j', ⟨hle, hτ⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · exact (Fin.castSucc_le_castSucc_iff.mpr hle)
    · exact (Fin.snoc_castSucc (α := fun _ => Bool) b τ j' ▸ hτ)
  · rintro ⟨hle, hσ⟩
    by_cases hi : i = Fin.last m
    · subst hi
      exfalso
      have hlt : j.castSucc < Fin.last m := Fin.castSucc_lt_last j
      omega
    · obtain ⟨j', rfl⟩ : ∃ j' : Fin m, j'.castSucc = i :=
      Fin.exists_castSucc_eq.mpr hi
      refine ⟨j', ⟨?_, ?_⟩, rfl⟩
      · exact (Fin.castSucc_le_castSucc_iff.mp hle)
      · have h := Fin.snoc_castSucc (α := fun _ => Bool) b τ j'
        rwa [h] at hσ

end MetaMathlibExt

namespace MetaMathlibExt

/--
[snoc_iic_false](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/BertrandBallot.lean)
-/
@[path]
private lemma snoc_iic_false {m : ℕ} (τ : Fin m → Bool) (b : Bool) (j : Fin m) :
  Finset.image Fin.castSucc (Finset.univ.filter (fun i : Fin m => i ≤ j ∧ τ i = false))
  = Finset.univ.filter (fun i : Fin (m + 1) =>
    i ≤ j.castSucc ∧ Fin.snoc (α := fun _ => Bool) τ b i = false) := by
  apply Finset.ext
  intro i
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j', ⟨hle, hτ⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · exact (Fin.castSucc_le_castSucc_iff.mpr hle)
    · exact (Fin.snoc_castSucc (α := fun _ => Bool) b τ j' ▸ hτ)
  · rintro ⟨hle, hσ⟩
    by_cases hi : i = Fin.last m
    · subst hi
      exfalso
      have hlt : j.castSucc < Fin.last m := Fin.castSucc_lt_last j
      omega
    · obtain ⟨j', rfl⟩ : ∃ j' : Fin m, j'.castSucc = i :=
      Fin.exists_castSucc_eq.mpr hi
      refine ⟨j', ⟨?_, ?_⟩, rfl⟩
      · exact (Fin.castSucc_le_castSucc_iff.mp hle)
      · have h := Fin.snoc_castSucc (α := fun _ => Bool) b τ j'
        rwa [h] at hσ

end MetaMathlibExt

namespace MetaMathlibExt

/--
[snoc_total_true_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/BertrandBallot.lean)
-/
@[path]
private lemma snoc_total_true_add {m : ℕ} (τ : Fin m → Bool) :
  (Finset.univ.filter (fun i : Fin (m + 1) =>
    Fin.snoc (α := fun _ => Bool) τ true i = true)).card
  = (Finset.univ.filter (fun i : Fin m => τ i = true)).card + 1 := by
  have hinj : Function.Injective (Fin.castSucc : Fin m → Fin (m + 1)) :=
    Fin.castSucc_injective m
  have hlast : Fin.snoc (α := fun _ => Bool) τ true (Fin.last m) = true :=
    Fin.snoc_last (α := fun _ => Bool) true τ
  have hdecomp : Finset.univ.filter (fun i : Fin (m + 1) =>
    Fin.snoc (α := fun _ => Bool) τ true i = true)
    = Finset.image Fin.castSucc (Finset.univ.filter (fun i : Fin m => τ i = true))
      ∪ {Fin.last m} := by
    apply Finset.ext
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_image, Finset.mem_singleton]
    constructor
    · intro hi
      by_cases heq : i = Fin.last m
      · exact Or.inr heq
      · obtain ⟨j, rfl⟩ : ∃ j : Fin m, j.castSucc = i :=
        Fin.exists_castSucc_eq.mpr heq
        refine Or.inl ⟨j, ?_, rfl⟩
        have h := Fin.snoc_castSucc (α := fun _ => Bool) true τ j
        rwa [h] at hi
    · rintro (⟨j, hj, rfl⟩ | rfl)
      · exact (Fin.snoc_castSucc (α := fun _ => Bool) true τ j ▸ hj)
      · exact hlast
  have hdisj : Disjoint
    (Finset.image Fin.castSucc (Finset.univ.filter (fun i : Fin m => τ i = true)))
    {Fin.last m} := by
    rw [Finset.disjoint_singleton_right]
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    rintro ⟨j, _, hj⟩
    have hlt := Fin.castSucc_lt_last j
    rw [hj] at hlt
    exact lt_irrefl _ hlt
  rw [hdecomp, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ hinj, Finset.card_singleton]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[snoc_total_true_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/BertrandBallot.lean)
-/
@[path]
private lemma snoc_total_true_eq {m : ℕ} (τ : Fin m → Bool) :
  (Finset.univ.filter (fun i : Fin (m + 1) =>
    Fin.snoc (α := fun _ => Bool) τ false i = true)).card
  = (Finset.univ.filter (fun i : Fin m => τ i = true)).card := by
  have hinj : Function.Injective (Fin.castSucc : Fin m → Fin (m + 1)) :=
    Fin.castSucc_injective m
  have hlast : Fin.snoc (α := fun _ => Bool) τ false (Fin.last m) = false :=
    Fin.snoc_last (α := fun _ => Bool) false τ
  have hdecomp : Finset.univ.filter (fun i : Fin (m + 1) =>
    Fin.snoc (α := fun _ => Bool) τ false i = true)
    = Finset.image Fin.castSucc (Finset.univ.filter (fun i : Fin m => τ i = true)) := by
    apply Finset.ext
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hi
      by_cases heq : i = Fin.last m
      · subst heq; rw [hlast] at hi; simp at hi
      · obtain ⟨j, rfl⟩ : ∃ j : Fin m, j.castSucc = i :=
        Fin.exists_castSucc_eq.mpr heq
        refine ⟨j, ?_, rfl⟩
        have h := Fin.snoc_castSucc (α := fun _ => Bool) false τ j
        rwa [h] at hi
    · rintro ⟨j, hj, rfl⟩
      exact (Fin.snoc_castSucc (α := fun _ => Bool) false τ j ▸ hj)
  rw [hdecomp, Finset.card_image_of_injective _ hinj]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[sigma_eq_snoc_init](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/BertrandBallot.lean)
-/
@[path]
private lemma sigma_eq_snoc_init {m : ℕ} (σ : Fin (m + 1) → Bool) :
  σ = Fin.snoc (α := fun _ => Bool) (Fin.init σ) (σ (Fin.last m)) := by
  funext i
  induction i using Fin.lastCases with
  | last => exact (Fin.snoc_last (α := fun _ => Bool) _ _).symm
  | cast j =>
    show σ j.castSucc
      = Fin.snoc (α := fun _ => Bool) (Fin.init σ) (σ (Fin.last m)) j.castSucc
    rw [Fin.snoc_castSucc (α := fun _ => Bool)]
    rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ballot_fwd_true](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/BertrandBallot.lean)
-/
@[path]
private lemma ballot_fwd_true {m : ℕ} {τ : Fin m → Bool}
  (hballot : ∀ k : Fin (m + 1),
    (Finset.univ.filter (fun i : Fin (m + 1) =>
      i ≤ k ∧ Fin.snoc (α := fun _ => Bool) τ true i = true)).card >
    (Finset.univ.filter (fun i : Fin (m + 1) =>
      i ≤ k ∧ Fin.snoc (α := fun _ => Bool) τ true i = false)).card) (j : Fin m) :
  (Finset.univ.filter (fun i : Fin m => i ≤ j ∧ τ i = true)).card >
  (Finset.univ.filter (fun i : Fin m => i ≤ j ∧ τ i = false)).card := by
  have hinj : Function.Injective (Fin.castSucc : Fin m → Fin (m + 1)) :=
    Fin.castSucc_injective m
  have hT := snoc_iic_true τ true j
  have hF := snoc_iic_false τ true j
  have hTcard : (Finset.univ.filter (fun i : Fin m => i ≤ j ∧ τ i = true)).card
    = (Finset.univ.filter (fun i : Fin (m + 1) =>
      i ≤ j.castSucc ∧ Fin.snoc (α := fun _ => Bool) τ true i = true)).card := by
    rw [← hT, Finset.card_image_of_injective _ hinj]
  have hFcard : (Finset.univ.filter (fun i : Fin m => i ≤ j ∧ τ i = false)).card
    = (Finset.univ.filter (fun i : Fin (m + 1) =>
      i ≤ j.castSucc ∧ Fin.snoc (α := fun _ => Bool) τ true i = false)).card := by
    rw [← hF, Finset.card_image_of_injective _ hinj]
  rw [hTcard, hFcard]
  exact hballot j.castSucc

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ballot_bwd_true_last](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/BertrandBallot.lean)
-/
@[path]
private lemma ballot_bwd_true_last {m p q : ℕ} {τ : Fin m → Bool}
  (hm : m + 1 = p + q)
  (hcount : (Finset.univ.filter (fun i : Fin m => τ i = true)).card = p - 1)
  (hlt : q < p) :
  (Finset.univ.filter (fun i : Fin (m + 1) =>
    i ≤ Fin.last m ∧ Fin.snoc (α := fun _ => Bool) τ true i = true)).card >
  (Finset.univ.filter (fun i : Fin (m + 1) =>
    i ≤ Fin.last m ∧ Fin.snoc (α := fun _ => Bool) τ true i = false)).card := by
  have hle_max : ∀ i : Fin (m + 1), i ≤ Fin.last m := fun i => Fin.le_last i
  have hT : (Finset.univ.filter (fun i : Fin (m + 1) =>
    i ≤ Fin.last m ∧ Fin.snoc (α := fun _ => Bool) τ true i = true)).card = p := by
    have hfilter : Finset.univ.filter (fun i : Fin (m + 1) =>
      i ≤ Fin.last m ∧ Fin.snoc (α := fun _ => Bool) τ true i = true)
      = Finset.univ.filter (fun i : Fin (m + 1) =>
        Fin.snoc (α := fun _ => Bool) τ true i = true) := by
      apply Finset.filter_congr
      intro i _
      simp [hle_max i]
    rw [hfilter, snoc_total_true_add]
    omega
  have hF : (Finset.univ.filter (fun i : Fin (m + 1) =>
    i ≤ Fin.last m ∧ Fin.snoc (α := fun _ => Bool) τ true i = false)).card = q := by
    have hfilter : Finset.univ.filter (fun i : Fin (m + 1) =>
      i ≤ Fin.last m ∧ Fin.snoc (α := fun _ => Bool) τ true i = false)
      = Finset.univ.filter (fun i : Fin (m + 1) =>
        Fin.snoc (α := fun _ => Bool) τ true i = false) := by
      apply Finset.filter_congr
      intro i _
      simp [hle_max i]
    rw [hfilter]
    have hTt : (Finset.univ.filter (fun i : Fin (m + 1) =>
      Fin.snoc (α := fun _ => Bool) τ true i = true)).card = p := by
      rw [snoc_total_true_add]
      omega
    have hcard := ballot_false_card (n := m + 1) (p := p)
      (σ := Fin.snoc (α := fun _ => Bool) τ true) hTt
    have hnp : m + 1 - p = q := by omega
    rwa [hnp] at hcard
  rw [hT, hF]
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ballot_fwd_false](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/BertrandBallot.lean)
-/
@[path]
private lemma ballot_fwd_false {m : ℕ} {τ : Fin m → Bool}
  (hballot : ∀ k : Fin (m + 1),
    (Finset.univ.filter (fun i : Fin (m + 1) =>
      i ≤ k ∧ Fin.snoc (α := fun _ => Bool) τ false i = true)).card >
    (Finset.univ.filter (fun i : Fin (m + 1) =>
      i ≤ k ∧ Fin.snoc (α := fun _ => Bool) τ false i = false)).card) (j : Fin m) :
  (Finset.univ.filter (fun i : Fin m => i ≤ j ∧ τ i = true)).card >
  (Finset.univ.filter (fun i : Fin m => i ≤ j ∧ τ i = false)).card := by
  have hinj : Function.Injective (Fin.castSucc : Fin m → Fin (m + 1)) :=
    Fin.castSucc_injective m
  have hT := snoc_iic_true τ false j
  have hF := snoc_iic_false τ false j
  have hTcard : (Finset.univ.filter (fun i : Fin m => i ≤ j ∧ τ i = true)).card
    = (Finset.univ.filter (fun i : Fin (m + 1) =>
      i ≤ j.castSucc ∧ Fin.snoc (α := fun _ => Bool) τ false i = true)).card := by
    rw [← hT, Finset.card_image_of_injective _ hinj]
  have hFcard : (Finset.univ.filter (fun i : Fin m => i ≤ j ∧ τ i = false)).card
    = (Finset.univ.filter (fun i : Fin (m + 1) =>
      i ≤ j.castSucc ∧ Fin.snoc (α := fun _ => Bool) τ false i = false)).card := by
    rw [← hF, Finset.card_image_of_injective _ hinj]
  rw [hTcard, hFcard]
  exact hballot j.castSucc

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ballot_bwd_false_last](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/BertrandBallot.lean)
-/
@[path]
private lemma ballot_bwd_false_last {m p q : ℕ} {τ : Fin m → Bool}
  (hm : m + 1 = p + q)
  (hcount : (Finset.univ.filter (fun i : Fin m => τ i = true)).card = p)
  (hlt : q < p) :
  (Finset.univ.filter (fun i : Fin (m + 1) =>
    i ≤ Fin.last m ∧ Fin.snoc (α := fun _ => Bool) τ false i = true)).card >
  (Finset.univ.filter (fun i : Fin (m + 1) =>
    i ≤ Fin.last m ∧ Fin.snoc (α := fun _ => Bool) τ false i = false)).card := by
  have hle_max : ∀ i : Fin (m + 1), i ≤ Fin.last m := fun i => Fin.le_last i
  have hT : (Finset.univ.filter (fun i : Fin (m + 1) =>
    i ≤ Fin.last m ∧ Fin.snoc (α := fun _ => Bool) τ false i = true)).card = p := by
    have hfilter : Finset.univ.filter (fun i : Fin (m + 1) =>
      i ≤ Fin.last m ∧ Fin.snoc (α := fun _ => Bool) τ false i = true)
      = Finset.univ.filter (fun i : Fin (m + 1) =>
        Fin.snoc (α := fun _ => Bool) τ false i = true) := by
      apply Finset.filter_congr
      intro i _
      simp [hle_max i]
    rwa [hfilter, snoc_total_true_eq]
  have hF : (Finset.univ.filter (fun i : Fin (m + 1) =>
    i ≤ Fin.last m ∧ Fin.snoc (α := fun _ => Bool) τ false i = false)).card = q := by
    have hfilter : Finset.univ.filter (fun i : Fin (m + 1) =>
      i ≤ Fin.last m ∧ Fin.snoc (α := fun _ => Bool) τ false i = false)
      = Finset.univ.filter (fun i : Fin (m + 1) =>
        Fin.snoc (α := fun _ => Bool) τ false i = false) := by
      apply Finset.filter_congr
      intro i _
      simp [hle_max i]
    rw [hfilter]
    have hTt : (Finset.univ.filter (fun i : Fin (m + 1) =>
      Fin.snoc (α := fun _ => Bool) τ false i = true)).card = p := by
      rwa [snoc_total_true_eq]
    have hcard := ballot_false_card (n := m + 1) (p := p)
      (σ := Fin.snoc (α := fun _ => Bool) τ false) hTt
    have hnp : m + 1 - p = q := by omega
    rwa [hnp] at hcard
  rw [hT, hF]
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[card_snoc_true](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/BertrandBallot.lean)
-/
@[path]
private lemma card_snoc_true {m P Q : ℕ} (hm : m = P + Q) (hlt : Q < P + 1) :
  (Finset.univ.filter (fun σ : Fin (m + 1) → Bool =>
    (Finset.univ.filter (fun i : Fin (m + 1) => σ i = true)).card = P + 1 ∧
    (∀ k : Fin (m + 1),
      (Finset.univ.filter (fun i : Fin (m + 1) => i ≤ k ∧ σ i = true)).card >
      (Finset.univ.filter (fun i : Fin (m + 1) => i ≤ k ∧ σ i = false)).card) ∧
    σ (Fin.last m) = true)).card
  = (Finset.univ.filter (fun τ : Fin m → Bool =>
    (Finset.univ.filter (fun i : Fin m => τ i = true)).card = P ∧
    ∀ k : Fin m,
      (Finset.univ.filter (fun i : Fin m => i ≤ k ∧ τ i = true)).card >
      (Finset.univ.filter (fun i : Fin m => i ≤ k ∧ τ i = false)).card)).card := by
  apply Finset.card_bij (fun σ _ => Fin.init σ)
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    obtain ⟨hcount, hballot, hlast⟩ := hσ
    have hσeq : σ = Fin.snoc (α := fun _ => Bool) (Fin.init σ) true := by
      have h := sigma_eq_snoc_init σ
      rwa [hlast] at h
    refine ⟨?_, ?_⟩
    · have hTeq : (Finset.univ.filter (fun i : Fin (m + 1) => σ i = true)).card
      = (Finset.univ.filter (fun i : Fin m => Fin.init σ i = true)).card + 1 := by
      conv_lhs => rw [hσeq]
      exact snoc_total_true_add _
      omega
    · intro j
      rw [hσeq] at hballot
      exact ballot_fwd_true hballot j
  · intro σ₁ h₁ σ₂ h₂ heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
    obtain ⟨_, _, hlast₁⟩ := h₁
    obtain ⟨_, _, hlast₂⟩ := h₂
    have e₁ : σ₁ = Fin.snoc (α := fun _ => Bool) (Fin.init σ₁) true := by
      have h := sigma_eq_snoc_init σ₁
      rwa [hlast₁] at h
    have e₂ : σ₂ = Fin.snoc (α := fun _ => Bool) (Fin.init σ₂) true := by
      have h := sigma_eq_snoc_init σ₂
      rwa [hlast₂] at h
    rw [e₁, e₂, heq]
  · intro τ hτ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ
    obtain ⟨hcount, hballot⟩ := hτ
    refine ⟨Fin.snoc (α := fun _ => Bool) τ true, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, ?_, ?_⟩
      · rw [snoc_total_true_add]
        omega
      · intro k
        by_cases hk : k = Fin.last m
        · subst hk
          have hm' : m + 1 = (P + 1) + Q := by omega
          have hc : (Finset.univ.filter (fun i : Fin m => τ i = true)).card = (P + 1) - 1 := by
            omega
          exact ballot_bwd_true_last hm' hc hlt
        · obtain ⟨j, rfl⟩ : ∃ j : Fin m, j.castSucc = k :=
          Fin.exists_castSucc_eq.mpr hk
          have hinj : Function.Injective (Fin.castSucc : Fin m → Fin (m + 1)) :=
            Fin.castSucc_injective m
          have hT : (Finset.univ.filter (fun i : Fin (m + 1) =>
            i ≤ j.castSucc ∧ Fin.snoc (α := fun _ => Bool) τ true i = true)).card
            = (Finset.univ.filter (fun i : Fin m => i ≤ j ∧ τ i = true)).card := by
            rw [← snoc_iic_true τ true j, Finset.card_image_of_injective _ hinj]
          have hF : (Finset.univ.filter (fun i : Fin (m + 1) =>
            i ≤ j.castSucc ∧ Fin.snoc (α := fun _ => Bool) τ true i = false)).card
            = (Finset.univ.filter (fun i : Fin m => i ≤ j ∧ τ i = false)).card := by
            rw [← snoc_iic_false τ true j, Finset.card_image_of_injective _ hinj]
          rw [hT, hF]
          exact hballot j
      · exact Fin.snoc_last (α := fun _ => Bool) true τ
    · exact Fin.init_snoc (α := fun _ => Bool) true τ

end MetaMathlibExt

namespace MetaMathlibExt

/--
[card_snoc_false](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/BertrandBallot.lean)
-/
@[path]
private lemma card_snoc_false {m P Q : ℕ} (hm : m = P + Q) (hlt : Q + 1 < P) :
  (Finset.univ.filter (fun σ : Fin (m + 1) → Bool =>
    (Finset.univ.filter (fun i : Fin (m + 1) => σ i = true)).card = P ∧
    (∀ k : Fin (m + 1),
      (Finset.univ.filter (fun i : Fin (m + 1) => i ≤ k ∧ σ i = true)).card >
      (Finset.univ.filter (fun i : Fin (m + 1) => i ≤ k ∧ σ i = false)).card) ∧
    σ (Fin.last m) = false)).card
  = (Finset.univ.filter (fun τ : Fin m → Bool =>
    (Finset.univ.filter (fun i : Fin m => τ i = true)).card = P ∧
    ∀ k : Fin m,
      (Finset.univ.filter (fun i : Fin m => i ≤ k ∧ τ i = true)).card >
      (Finset.univ.filter (fun i : Fin m => i ≤ k ∧ τ i = false)).card)).card := by
  apply Finset.card_bij (fun σ _ => Fin.init σ)
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    obtain ⟨hcount, hballot, hlast⟩ := hσ
    have hσeq : σ = Fin.snoc (α := fun _ => Bool) (Fin.init σ) false := by
      have h := sigma_eq_snoc_init σ
      rwa [hlast] at h
    refine ⟨?_, ?_⟩
    · have hTeq : (Finset.univ.filter (fun i : Fin (m + 1) => σ i = true)).card
      = (Finset.univ.filter (fun i : Fin m => Fin.init σ i = true)).card := by
      conv_lhs => rw [hσeq]
      exact snoc_total_true_eq _
      omega
    · intro j
      rw [hσeq] at hballot
      exact ballot_fwd_false hballot j
  · intro σ₁ h₁ σ₂ h₂ heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
    obtain ⟨_, _, hlast₁⟩ := h₁
    obtain ⟨_, _, hlast₂⟩ := h₂
    have e₁ : σ₁ = Fin.snoc (α := fun _ => Bool) (Fin.init σ₁) false := by
      have h := sigma_eq_snoc_init σ₁
      rwa [hlast₁] at h
    have e₂ : σ₂ = Fin.snoc (α := fun _ => Bool) (Fin.init σ₂) false := by
      have h := sigma_eq_snoc_init σ₂
      rwa [hlast₂] at h
    rw [e₁, e₂, heq]
  · intro τ hτ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ
    obtain ⟨hcount, hballot⟩ := hτ
    refine ⟨Fin.snoc (α := fun _ => Bool) τ false, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, ?_, ?_⟩
      · rw [snoc_total_true_eq]
        exact hcount
      · intro k
        by_cases hk : k = Fin.last m
        · subst hk
          have hm' : m + 1 = P + (Q + 1) := by omega
          exact ballot_bwd_false_last hm' hcount hlt
        · obtain ⟨j, rfl⟩ : ∃ j : Fin m, j.castSucc = k :=
          Fin.exists_castSucc_eq.mpr hk
          have hinj : Function.Injective (Fin.castSucc : Fin m → Fin (m + 1)) :=
            Fin.castSucc_injective m
          have hT : (Finset.univ.filter (fun i : Fin (m + 1) =>
            i ≤ j.castSucc ∧ Fin.snoc (α := fun _ => Bool) τ false i = true)).card
            = (Finset.univ.filter (fun i : Fin m => i ≤ j ∧ τ i = true)).card := by
            rw [← snoc_iic_true τ false j, Finset.card_image_of_injective _ hinj]
          have hF : (Finset.univ.filter (fun i : Fin (m + 1) =>
            i ≤ j.castSucc ∧ Fin.snoc (α := fun _ => Bool) τ false i = false)).card
            = (Finset.univ.filter (fun i : Fin m => i ≤ j ∧ τ i = false)).card := by
            rw [← snoc_iic_false τ false j, Finset.card_image_of_injective _ hinj]
          rw [hT, hF]
          exact hballot j
      · exact Fin.snoc_last (α := fun _ => Bool) false τ
    · exact Fin.init_snoc (α := fun _ => Bool) false τ

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ballot_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/BertrandBallot.lean)
-/
@[path]
private lemma ballot_recurrence {p' q' : ℕ} (hlt : q' + 1 < p' + 1) :
  (Finset.univ.filter (fun σ : Fin ((p' + 1) + (q' + 1)) → Bool =>
    (Finset.univ.filter (fun i => σ i = true)).card = (p' + 1) ∧
    (∀ k, (Finset.univ.filter (fun i => i ≤ k ∧ σ i = true)).card >
      (Finset.univ.filter (fun i => i ≤ k ∧ σ i = false)).card))).card
  = (Finset.univ.filter (fun τ : Fin (p' + (q' + 1)) → Bool =>
    (Finset.univ.filter (fun i => τ i = true)).card = p' ∧
    (∀ k, (Finset.univ.filter (fun i => i ≤ k ∧ τ i = true)).card >
      (Finset.univ.filter (fun i => i ≤ k ∧ τ i = false)).card))).card
  + (Finset.univ.filter (fun τ : Fin ((p' + 1) + q') → Bool =>
    (Finset.univ.filter (fun i => τ i = true)).card = (p' + 1) ∧
    (∀ k, (Finset.univ.filter (fun i => i ≤ k ∧ τ i = true)).card >
      (Finset.univ.filter (fun i => i ≤ k ∧ τ i = false)).card))).card := by
  set m := p' + q' + 1 with hm_def
  have hn : (p' + 1) + (q' + 1) = m + 1 := by omega
  have hm1 : m = p' + (q' + 1) := by omega
  have hm2 : m = (p' + 1) + q' := by omega
  rw [hn]
  set s := Finset.univ.filter (fun σ : Fin (m + 1) → Bool =>
    (Finset.univ.filter (fun i => σ i = true)).card = (p' + 1) ∧
    (∀ k, (Finset.univ.filter (fun i => i ≤ k ∧ σ i = true)).card >
      (Finset.univ.filter (fun i => i ≤ k ∧ σ i = false)).card)) with hs_def
  have hsplit := Finset.card_filter_add_card_filter_not (s := s)
    (fun σ : Fin (m + 1) → Bool => σ (Fin.last m) = true)
  have hnot : (Finset.univ.filter (fun σ : Fin (m + 1) → Bool =>
    (Finset.univ.filter (fun i => σ i = true)).card = (p' + 1) ∧
    (∀ k, (Finset.univ.filter (fun i => i ≤ k ∧ σ i = true)).card >
      (Finset.univ.filter (fun i => i ≤ k ∧ σ i = false)).card) ∧
    σ (Fin.last m) = false)).card
    = {a ∈ s | ¬ a (Fin.last m) = true}.card := by
    congr 1
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hs_def]
    constructor
    · intro h
      cases h' : σ (Fin.last m) <;> simp_all
    · intro h
      cases h' : σ (Fin.last m) <;> simp_all
  have hyes : (Finset.univ.filter (fun σ : Fin (m + 1) → Bool =>
    (Finset.univ.filter (fun i => σ i = true)).card = (p' + 1) ∧
    (∀ k, (Finset.univ.filter (fun i => i ≤ k ∧ σ i = true)).card >
      (Finset.univ.filter (fun i => i ≤ k ∧ σ i = false)).card) ∧
    σ (Fin.last m) = true)).card
    = (Finset.filter (fun σ : Fin (m + 1) → Bool => σ (Fin.last m) = true) s).card := by
    congr 1
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hs_def]
    constructor
    · intro h
      cases h' : σ (Fin.last m) <;> simp_all
    · intro h
      cases h' : σ (Fin.last m) <;> simp_all
  have hcard : s.card
    = (Finset.univ.filter (fun σ : Fin (m + 1) → Bool =>
      (Finset.univ.filter (fun i => σ i = true)).card = (p' + 1) ∧
      (∀ k, (Finset.univ.filter (fun i => i ≤ k ∧ σ i = true)).card >
        (Finset.univ.filter (fun i => i ≤ k ∧ σ i = false)).card) ∧
      σ (Fin.last m) = true)).card
    + (Finset.univ.filter (fun σ : Fin (m + 1) → Bool =>
      (Finset.univ.filter (fun i => σ i = true)).card = (p' + 1) ∧
      (∀ k, (Finset.univ.filter (fun i => i ≤ k ∧ σ i = true)).card >
        (Finset.univ.filter (fun i => i ≤ k ∧ σ i = false)).card) ∧
      σ (Fin.last m) = false)).card := by
    omega
  rw [hcard]
  congr 1
  · rw [← hm1]
    exact card_snoc_true hm1 hlt
  · rw [← hm2]
    exact card_snoc_false hm2 hlt

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ballot_all](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/BertrandBallot.lean)
-/
@[path]
private lemma ballot_all : ∀ n p q : ℕ, p + q = n →
  (Finset.univ.filter (fun σ : Fin (p + q) → Bool =>
    (Finset.univ.filter (fun i : Fin (p + q) => σ i = true)).card = p ∧
    ∀ k : Fin (p + q),
      (Finset.univ.filter (fun i : Fin (p + q) => i ≤ k ∧ σ i = true)).card >
      (Finset.univ.filter (fun i : Fin (p + q) => i ≤ k ∧ σ i = false)).card)).card
  * (p + q) = (p - q) * (p + q).choose q := by
  intro n
  induction n with
  | zero =>
    intro p q h
    have hp : p = 0 := by omega
    have hq : q = 0 := by omega
    subst hp
    subst hq
    simp
  | succ n ih =>
    intro p q h
    by_cases hle : p ≤ q
    · by_cases hpos : 0 < p + q
      · have hF := ballot_eq_zero_of_le hle hpos
        have hsub : p - q = 0 := Nat.sub_eq_zero_of_le hle
        rw [hF, hsub, Nat.zero_mul, Nat.zero_mul]
      · have hp0 : p = 0 := by omega
        have hq0 : q = 0 := by omega
        subst hp0
        subst hq0
        simp
    · have hlt : q < p := by omega
      by_cases hq0 : q = 0
      · subst hq0
        have hp0 : 0 < p := by omega
        simp only [Nat.add_zero]
        have hF := ballot_one_of_zero hp0
        rw [hF, Nat.sub_zero, Nat.choose_zero_right, Nat.one_mul, Nat.mul_one]
      · have hq1 : 1 ≤ q := by omega
        obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
        obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
        have hlt' : q' + 1 < p' + 1 := by omega
        have hrec := ballot_recurrence hlt'
        have hm : p' + (q' + 1) = n := by omega
        have hm2 : (p' + 1) + q' = n := by omega
        have ih1 := ih p' (q' + 1) hm
        have ih2 := ih (p' + 1) q' hm2
        have h1 : (Finset.univ.filter (fun τ : Fin (p' + (q' + 1)) → Bool =>
          (Finset.univ.filter (fun i : Fin (p' + (q' + 1)) => τ i = true)).card = p' ∧
          ∀ k : Fin (p' + (q' + 1)),
            (Finset.univ.filter (fun i : Fin (p' + (q' + 1)) => i ≤ k ∧ τ i = true)).card >
            (Finset.univ.filter (fun i : Fin (p' + (q' + 1)) => i ≤ k ∧ τ i = false)).card)).card
          * (((p' + 1) + (q' + 1)) - 1)
          = (((p' + 1) - 1 - (q' + 1)))
            * ((((p' + 1) + (q' + 1)) - 1).choose (q' + 1)) := by
          have eS : ((p' + 1) + (q' + 1)) - 1 = p' + (q' + 1) := by omega
          have eA : (p' + 1) - 1 - (q' + 1) = p' - (q' + 1) := by omega
          rwa [eS, eA]
        have h2 : (Finset.univ.filter (fun τ : Fin ((p' + 1) + q') → Bool =>
          (Finset.univ.filter (fun i : Fin ((p' + 1) + q') => τ i = true)).card = (p' + 1) ∧
          ∀ k : Fin ((p' + 1) + q'),
            (Finset.univ.filter (fun i : Fin ((p' + 1) + q') => i ≤ k ∧ τ i = true)).card >
            (Finset.univ.filter (fun i : Fin ((p' + 1) + q') => i ≤ k ∧ τ i = false)).card)).card
          * (((p' + 1) + (q' + 1)) - 1)
          = (((p' + 1) - ((q' + 1) - 1)))
            * ((((p' + 1) + (q' + 1)) - 1).choose ((q' + 1) - 1)) := by
          have eS : ((p' + 1) + (q' + 1)) - 1 = (p' + 1) + q' := by omega
          have eC : ((p' + 1) - ((q' + 1) - 1)) = ((p' + 1) - q') := by omega
          have eQ : ((q' + 1) - 1) = q' := by omega
          rwa [eS, eC, eQ]
        rw [hrec]
        exact ballot_arith (by omega) hlt' h1 h2

end MetaMathlibExt

namespace MetaMathlibExt

/--
[bertrand_ballot](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/BertrandBallot.lean)
-/
@[path]
lemma bertrand_ballot
  :
-- imply
  ∀ (p q : ℕ), 1 ≤ q → q < p →
    (Finset.univ.filter (fun σ : Fin (p + q) → Bool =>
    (Finset.univ.filter (fun i : Fin (p + q) => σ i = true)).card = p ∧
    ∀ k : Fin (p + q),
    (Finset.univ.filter (fun i : Fin (p + q) => i ≤ k ∧ σ i = true)).card >
    (Finset.univ.filter (fun i : Fin (p + q) => i ≤ k ∧ σ i = false)).card)).card
    * (p + q) = (p - q) * (p + q).choose q := by
-- proof
  intro p q hq hlt
  exact ballot_all (p + q) p q rfl

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26

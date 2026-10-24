/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace MetaMathlibExt

/-! # Peak generating function for set partitions, Chebyshev form

This file proves the Mansour-Shattuck peak generating function for set partitions,
encoded as surjective restricted-growth strings.
-/

/-- A surjective restricted-growth string: every label smaller than the label
at position `i` already occurs at an earlier position. -/
def IsSurjectiveRestrictedGrowthString {n k : ℕ} (w : Fin n → Fin k) : Prop :=
  Function.Surjective w ∧
    ∀ i : Fin n, ∀ m : Fin k,
      m.val < (w i).val → ∃ j : Fin n, j.val < i.val ∧ w j = m

/-- Decidability of the restricted-growth predicate (finite quantification). -/
instance (n k : ℕ) : DecidablePred (@IsSurjectiveRestrictedGrowthString n k) := by
  intro w
  unfold IsSurjectiveRestrictedGrowthString Function.Surjective
  infer_instance

private abbrev pgfR := PowerSeries (Polynomial ℤ)

private abbrev pgfK := FractionRing pgfR

private noncomputable def pgf_x : pgfR := PowerSeries.X

private noncomputable def pgf_q : pgfR := PowerSeries.C Polynomial.X

private noncomputable def pgf_y : pgfR := pgf_x ^ 2 * (1 - pgf_q)

private noncomputable def pgf_G : ℕ → pgfR
  | 0 => 1
  | 1 => 1
  | n + 2 => (2 + pgf_y) * pgf_G (n + 1) - pgf_G n

private noncomputable def pgf_map (f : pgfR) : pgfK :=
  algebraMap pgfR pgfK f

private noncomputable def pgf_t : pgfK :=
  1 + pgf_map pgf_x ^ 2 * (1 - pgf_map pgf_q) / 2

private noncomputable def pgf_U (m : ℤ) : pgfK :=
  (Polynomial.Chebyshev.U pgfK m).eval pgf_t

private noncomputable def pgf_A : pgfR := pgf_x * (pgf_q - 1)

private noncomputable def pgf_B : pgfR := 1 - pgf_x * (pgf_q - 1)

private noncomputable def pgf_C : pgfR :=
  1 - pgf_x * (1 - pgf_q) * (1 - pgf_x)

private noncomputable def pgf_D : pgfR :=
  -pgf_x * (pgf_x + pgf_q * (1 - pgf_x))

private def pgf_isPeakAt {n m : ℕ} (w : Fin n → Fin m) (i : Fin n) : Prop :=
  i.val ≠ 0 ∧
    if h : i.val + 1 < n then
      w ⟨i.val - 1, lt_of_le_of_lt (Nat.sub_le i.val 1) i.isLt⟩ < w i ∧
        w ⟨i.val + 1, h⟩ < w i
    else False

private instance {n m : ℕ} (w : Fin n → Fin m) : DecidablePred (pgf_isPeakAt w) := by
  intro i
  unfold pgf_isPeakAt
  infer_instance

private def pgf_peak {n m : ℕ} (w : Fin n → Fin m) : ℕ :=
  (Finset.univ.filter (pgf_isPeakAt w)).card

private def pgf_peakTriples {n m : ℕ} (w : Fin n → Fin m) : ℕ :=
  (Finset.univ.filter fun s : Fin n × Fin n × Fin n =>
    s.1.val + 1 = s.2.1.val ∧ s.2.1.val + 1 = s.2.2.val ∧
      w s.1 < w s.2.1 ∧ w s.2.2 < w s.2.1).card

private noncomputable def pgf_W (m : ℕ) : pgfR :=
  PowerSeries.mk fun n => ∑ w : Fin n → Fin m, Polynomial.X ^ pgf_peak w

private noncomputable def pgf_PP (k : ℕ) : pgfR :=
  PowerSeries.mk fun n => ∑ w ∈ Finset.univ.filter
    (fun w : Fin n → Fin k => IsSurjectiveRestrictedGrowthString w),
    Polynomial.X ^ pgf_peak w

private def pgf_peakNat {m K : ℕ} (w : Fin m → Fin K) (v : ℕ) : ℕ :=
  if h : v < m then
    if _ : 0 < v then
      if hv1 : v + 1 < m then
        if w ⟨v - 1, lt_of_le_of_lt (Nat.sub_le v 1) h⟩ < w ⟨v, h⟩ ∧
            w ⟨v + 1, hv1⟩ < w ⟨v, h⟩ then 1 else 0
      else 0
    else 0
  else 0

private abbrev pgfFirstData (n m : ℕ) :=
  Σ i : Fin n, (Fin i.val → Fin m) × (Fin (n - 1 - i.val) → Fin (m + 1))

private def pgf_joinFirst {n m : ℕ} (d : pgfFirstData n m) : Fin n → Fin (m + 1) :=
  fun j =>
    if hlt : j.val < d.1.val then d.2.1 ⟨j.val, hlt⟩ |>.castSucc
    else if heq : j.val = d.1.val then Fin.last m
    else d.2.2 ⟨j.val - d.1.val - 1, by omega⟩

private lemma pgf_joinFirst_top {n m : ℕ} (d : pgfFirstData n m) :
    pgf_joinFirst d d.1 = Fin.last m := by
  simp [pgf_joinFirst]

private lemma pgf_joinFirst_before {n m : ℕ} (i : Fin n) (u : Fin i.val → Fin m)
    (v : Fin (n - 1 - i.val) → Fin (m + 1)) (j : Fin i.val) :
    pgf_joinFirst ⟨i, u, v⟩ ⟨j.val, lt_trans j.isLt i.isLt⟩ = (u j).castSucc := by
  simp [pgf_joinFirst, j.isLt]

private lemma pgf_joinFirst_after {n m : ℕ} (i : Fin n) (u : Fin i.val → Fin m)
    (v : Fin (n - 1 - i.val) → Fin (m + 1)) (j : Fin (n - 1 - i.val)) :
    pgf_joinFirst ⟨i, u, v⟩ ⟨i.val + 1 + j.val, by omega⟩ = v j := by
  unfold pgf_joinFirst
  dsimp
  have hnlt : ¬i.val + 1 + j.val < i.val := by omega
  have hneq : i.val + 1 + j.val ≠ i.val := by omega
  rw [dite_eq_right hnlt, dite_eq_right hneq]
  congr 1
  apply Fin.ext
  change (i.val + 1 + j.val - i.val - 1) = j.val
  omega

private lemma pgf_joinFirst_top_le {n m : ℕ} (d : pgfFirstData n m) (j : Fin n)
    (h : pgf_joinFirst d j = Fin.last m) : d.1.val ≤ j.val := by
  by_contra hnle
  have hlt : j.val < d.1.val := by omega
  unfold pgf_joinFirst at h
  rw [dite_eq_left hlt] at h
  exact Fin.castSucc_ne_last _ h

private lemma pgf_joinFirst_injective (n m : ℕ) :
    Function.Injective (@pgf_joinFirst n m) := by
  rintro ⟨i, u, v⟩ ⟨i', u', v'⟩ h
  have hii' : i.val ≤ i'.val := by
    apply pgf_joinFirst_top_le ⟨i, u, v⟩ i'
    have hi' := congrFun h i'
    rw [pgf_joinFirst_top] at hi'
    exact hi'
  have hi'i : i'.val ≤ i.val := by
    apply pgf_joinFirst_top_le ⟨i', u', v'⟩ i
    have hi := congrFun h i
    rw [pgf_joinFirst_top] at hi
    exact hi.symm
  have heq : i = i' := Fin.ext (by omega)
  subst i'
  have hu : u = u' := by
    funext j
    apply Fin.castSucc_injective
    have hj := congrFun h ⟨j.val, lt_trans j.isLt i.isLt⟩
    simpa only [pgf_joinFirst_before] using hj
  have hv : v = v' := by
    funext j
    have hj := congrFun h ⟨i.val + 1 + j.val, by omega⟩
    simpa only [pgf_joinFirst_after] using hj
  subst u'
  subst v'
  rfl

private def pgf_decodeFirst (n m : ℕ) :
    (Fin n → Fin m) ⊕ pgfFirstData n m → Fin n → Fin (m + 1)
  | Sum.inl u => Fin.castSucc ∘ u
  | Sum.inr d => pgf_joinFirst d

private lemma pgf_decodeFirst_injective (n m : ℕ) :
    Function.Injective (pgf_decodeFirst n m) := by
  rintro (u | d) (u' | d') h
  · congr 1
    funext j
    apply Fin.castSucc_injective
    exact congrFun h j
  · have hi := congrFun h d'.1
    simp only [pgf_decodeFirst, Function.comp_apply, pgf_joinFirst_top] at hi
    exact False.elim (Fin.castSucc_ne_last _ hi)
  · have hi := congrFun h d.1
    simp only [pgf_decodeFirst, Function.comp_apply, pgf_joinFirst_top] at hi
    exact False.elim (Fin.castSucc_ne_last _ hi.symm)
  · congr 1
    exact pgf_joinFirst_injective n m h

private lemma pgf_decodeFirst_surjective (n m : ℕ) :
    Function.Surjective (pgf_decodeFirst n m) := by
  intro w
  by_cases htop : ∃ i, w i = Fin.last m
  · have hex : ∃ r : ℕ, ∃ hr : r < n, w ⟨r, hr⟩ = Fin.last m := by
      obtain ⟨i, hi⟩ := htop
      exact ⟨i.val, i.isLt, hi⟩
    let p := Nat.find hex
    have hpspec : ∃ hp : p < n, w ⟨p, hp⟩ = Fin.last m := by
      simpa [p] using Nat.find_spec hex
    obtain ⟨hp, hptop⟩ := hpspec
    have hbefore : ∀ r < p, ∀ hr : r < n, w ⟨r, hr⟩ ≠ Fin.last m := by
      intro r hr hrn heq
      exact (Nat.find_min hex (by simpa [p] using hr)) ⟨hrn, heq⟩
    let i : Fin n := ⟨p, hp⟩
    let u : Fin p → Fin m := fun j =>
      (w ⟨j.val, lt_trans j.isLt hp⟩).castPred (hbefore j.val j.isLt _)
    let v : Fin (n - 1 - p) → Fin (m + 1) := fun j =>
      w ⟨p + 1 + j.val, by omega⟩
    refine ⟨Sum.inr ⟨i, u, v⟩, ?_⟩
    funext j
    change pgf_joinFirst ⟨i, u, v⟩ j = w j
    unfold pgf_joinFirst
    dsimp only [i]
    by_cases hjp : j.val < p
    · rw [dite_eq_left hjp]
      dsimp only [u]
      rw [Fin.castSucc_castPred]
    · rw [dite_eq_right hjp]
      by_cases hjpeq : j.val = p
      · rw [dite_eq_left hjpeq]
        have hji : j = ⟨p, hp⟩ := Fin.ext hjpeq
        rw [hji, hptop]
      · rw [dite_eq_right hjpeq]
        dsimp only [v]
        congr 1
        apply Fin.ext
        dsimp
        omega
  · let u : Fin n → Fin m := fun i => (w i).castPred (fun hi => htop ⟨i, hi⟩)
    refine ⟨Sum.inl u, ?_⟩
    funext i
    change (u i).castSucc = w i
    exact Fin.castSucc_castPred _ _

private noncomputable def pgf_firstTopEquiv (n m : ℕ) :
    ((Fin n → Fin m) ⊕ pgfFirstData n m) ≃ (Fin n → Fin (m + 1)) :=
  Equiv.ofBijective (pgf_decodeFirst n m)
    ⟨pgf_decodeFirst_injective n m, pgf_decodeFirst_surjective n m⟩

@[simp] private lemma pgf_last_not_lt_castSucc {m : ℕ} (a : Fin m) :
    ¬Fin.last m < a.castSucc :=
  fun h => (Fin.castSucc_lt_last a).asymm h

@[simp] private lemma pgf_last_not_lt {m : ℕ} (a : Fin (m + 1)) :
    ¬Fin.last m < a :=
  not_lt_of_ge (Fin.le_last a)

private def pgf_boundary {n m : ℕ} (d : pgfFirstData n m) : ℕ :=
  if _ : 0 < d.1.val then
    if hv : 0 < n - 1 - d.1.val then
      if d.2.2 ⟨0, hv⟩ < Fin.last m then 1 else 0
    else 0
  else 0

private noncomputable def pgf_L (m : ℕ) : pgfR :=
  PowerSeries.mk fun n =>
    if h : 0 < n then
      ∑ w ∈ Finset.univ.filter (fun w : Fin n → Fin (m + 1) =>
        w ⟨0, h⟩ < Fin.last m), (Polynomial.X : Polynomial ℤ) ^ pgf_peak w
    else 0

private noncomputable def pgf_H (m : ℕ) : pgfR :=
  PowerSeries.mk fun n =>
    ∑ d : pgfFirstData n m, (Polynomial.X : Polynomial ℤ) ^ pgf_peak (pgf_joinFirst d)

private noncomputable def pgf_den (m : ℕ) : pgfR :=
  pgf_G (m + 1) - pgf_B * pgf_G m

private lemma pgf_rg_join_iff {n k : ℕ} (i : Fin n) (u : Fin i.val → Fin k)
    (v : Fin (n - 1 - i.val) → Fin (k + 1)) :
    IsSurjectiveRestrictedGrowthString (pgf_joinFirst ⟨i, u, v⟩) ↔
      IsSurjectiveRestrictedGrowthString u := by
  constructor
  · rintro ⟨_, hgrowth⟩
    constructor
    · intro a
      have halt : a.castSucc < Fin.last k := Fin.castSucc_lt_last a
      obtain ⟨j, hji, hj⟩ := hgrowth i a.castSucc (by
        rw [pgf_joinFirst_top]
        exact halt)
      let j' : Fin i.val := ⟨j.val, hji⟩
      refine ⟨j', ?_⟩
      apply Fin.castSucc_injective
      calc
        (u j').castSucc = pgf_joinFirst ⟨i, u, v⟩
            ⟨j'.val, lt_trans j'.isLt i.isLt⟩ := (pgf_joinFirst_before i u v j').symm
        _ = pgf_joinFirst ⟨i, u, v⟩ j := by
          congr 1
        _ = a.castSucc := hj
    · intro j a ha
      let jg : Fin n := ⟨j.val, lt_trans j.isLt i.isLt⟩
      have hjg : pgf_joinFirst ⟨i, u, v⟩ jg = (u j).castSucc := by
        exact pgf_joinFirst_before i u v j
      obtain ⟨l, hlj, hl⟩ := hgrowth jg a.castSucc (by
        rw [hjg]
        exact Fin.castSucc_lt_castSucc_iff.mpr ha)
      let l' : Fin i.val := ⟨l.val, lt_trans hlj j.isLt⟩
      refine ⟨l', hlj, ?_⟩
      apply Fin.castSucc_injective
      calc
        (u l').castSucc = pgf_joinFirst ⟨i, u, v⟩
            ⟨l'.val, lt_trans l'.isLt i.isLt⟩ := (pgf_joinFirst_before i u v l').symm
        _ = pgf_joinFirst ⟨i, u, v⟩ l := by
          congr 1
        _ = a.castSucc := hl
  · rintro ⟨hsurj, hgrowth⟩
    constructor
    · intro a
      by_cases ha : a = Fin.last k
      · exact ⟨i, by simpa [ha] using pgf_joinFirst_top ⟨i, u, v⟩⟩
      · obtain ⟨j, hj⟩ := hsurj (a.castPred ha)
        refine ⟨⟨j.val, lt_trans j.isLt i.isLt⟩, ?_⟩
        rw [show (⟨j.val, lt_trans j.isLt i.isLt⟩ : Fin n) =
            ⟨j.val, lt_trans j.isLt i.isLt⟩ by rfl,
          pgf_joinFirst_before]
        rw [hj, Fin.castSucc_castPred]
    · intro j a ha
      by_cases hji : j.val < i.val
      · let j' : Fin i.val := ⟨j.val, hji⟩
        have hj : pgf_joinFirst ⟨i, u, v⟩ j = (u j').castSucc := by
          calc
            pgf_joinFirst ⟨i, u, v⟩ j = pgf_joinFirst ⟨i, u, v⟩
                ⟨j'.val, lt_trans j'.isLt i.isLt⟩ := by
              congr 1
            _ = (u j').castSucc := pgf_joinFirst_before i u v j'
        have hane : a ≠ Fin.last k := by
          intro hatop
          rw [hatop, hj] at ha
          exact (Fin.castSucc_lt_last (u j')).asymm ha
        let a' : Fin k := a.castPred hane
        have haj : a' < u j' := by
          apply Fin.castSucc_lt_castSucc_iff.mp
          simpa only [a', Fin.castSucc_castPred] using (hj ▸ ha)
        obtain ⟨l, hlj, hl⟩ := hgrowth j' a' haj
        refine ⟨⟨l.val, lt_trans (lt_trans hlj j'.isLt) i.isLt⟩, ?_, ?_⟩
        · exact hlj
        · rw [pgf_joinFirst_before]
          simp only [hl, a', Fin.castSucc_castPred]
      · by_cases haTop : a = Fin.last k
        · rw [haTop] at ha
          exact False.elim ((not_lt_of_ge (Fin.le_last _)) ha)
        · obtain ⟨l, hl⟩ := hsurj (a.castPred haTop)
          refine ⟨⟨l.val, lt_trans l.isLt i.isLt⟩, ?_, ?_⟩
          · exact lt_of_lt_of_le l.isLt (Nat.le_of_not_gt hji)
          · rw [pgf_joinFirst_before, hl, Fin.castSucc_castPred]

private def pgf_rgJoinMap (n k : ℕ) :
    {d : pgfFirstData n k // IsSurjectiveRestrictedGrowthString d.2.1} →
      {w : Fin n → Fin (k + 1) // IsSurjectiveRestrictedGrowthString w} :=
  fun d => ⟨pgf_joinFirst d.val,
    (pgf_rg_join_iff d.val.1 d.val.2.1 d.val.2.2).2 d.property⟩

private lemma pgf_rgJoinMap_injective (n k : ℕ) :
    Function.Injective (pgf_rgJoinMap n k) := by
  intro d₁ d₂ h
  apply Subtype.ext
  apply pgf_joinFirst_injective n k
  simpa [pgf_rgJoinMap] using congrArg Subtype.val h

private lemma pgf_rgJoinMap_surjective (n k : ℕ) :
    Function.Surjective (pgf_rgJoinMap n k) := by
  intro w
  obtain ⟨z, hz⟩ := pgf_decodeFirst_surjective n k w
  cases z with
  | inl u =>
      obtain ⟨j, hj⟩ := w.property.1 (Fin.last k)
      have hc := congrFun hz j
      simp only [pgf_decodeFirst, Function.comp_apply] at hc
      exact False.elim (Fin.castSucc_ne_last _ (hc.trans hj))
  | inr d =>
      have hz' : pgf_joinFirst d = w := by simpa [pgf_decodeFirst] using hz
      have hdjoin : IsSurjectiveRestrictedGrowthString (pgf_joinFirst d) := by
        rw [hz']
        exact w.property
      let d' : {d : pgfFirstData n k // IsSurjectiveRestrictedGrowthString d.2.1} :=
        ⟨d, (pgf_rg_join_iff d.1 d.2.1 d.2.2).1 hdjoin⟩
      refine ⟨d', ?_⟩
      apply Subtype.ext
      simpa [pgf_rgJoinMap] using hz'

private noncomputable def pgf_rgJoinEquiv (n k : ℕ) :
    {d : pgfFirstData n k // IsSurjectiveRestrictedGrowthString d.2.1} ≃
      {w : Fin n → Fin (k + 1) // IsSurjectiveRestrictedGrowthString w} :=
  Equiv.ofBijective (pgf_rgJoinMap n k)
    ⟨pgf_rgJoinMap_injective n k, pgf_rgJoinMap_surjective n k⟩

private noncomputable def pgf_PH (k : ℕ) : pgfR :=
  PowerSeries.mk fun n =>
    ∑ d ∈ Finset.univ.filter
      (fun d : pgfFirstData n k => IsSurjectiveRestrictedGrowthString d.2.1),
      (Polynomial.X : Polynomial ℤ) ^ pgf_peak (pgf_joinFirst d)

private noncomputable def pgf_F (j : ℕ) : pgfR :=
  1 + pgf_x * (1 - pgf_q) * pgf_W j + pgf_q * (pgf_W j - 1)

private noncomputable def pgf_r (j : ℕ) : pgfK :=
  pgf_map (pgf_G (j + 1)) / pgf_map (pgf_G j)
end MetaMathlibExt

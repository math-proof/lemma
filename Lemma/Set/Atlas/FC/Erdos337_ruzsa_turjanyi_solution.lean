import Mathlib
import sympy.Basic
import Def.FC.Erdos337_ruzsa_turjanyi_solution
open Erdos337
open Filter Set Asymptotics
open scoped Pointwise


namespace Erdos337

/--
[mem_trunc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/Erdos337_ruzsa_turjanyi_solution.lean)
-/
@[path]
lemma mem_trunc
  {A : Set ℕ}
  {N : ℕ}
  {x : ℤ} :
-- imply
  x ∈ trunc A N ↔ ∃ n : ℕ, n ∈ A ∧ n ≤ N ∧ (n : ℤ) = x := by
-- proof
  simp [trunc]
  aesop

end Erdos337

namespace Erdos337

/--
[basis_card_le_iterated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/Erdos337_ruzsa_turjanyi_solution.lean)
-/
@[path]
lemma basis_card_le_iterated
  {A : Set ℕ}
  {h : ℕ}
-- given
  (hb : A.IsAsymptoticAddBasisOfOrder h) :
-- imply
  ∀ᶠ N : ℕ in atTop, (N : ℝ) / 2 ≤ ((h • trunc A N).card : ℝ) := by
-- proof
  rw [Set.isAsymptoticAddBasisOfOrder_iff_sum, Nat.cofinite_eq_atTop,
    eventually_atTop] at hb
  obtain ⟨M, hM⟩ := hb
  filter_upwards [eventually_ge_atTop (2 * M)] with N hN
  have hsub : (Finset.Icc M N).image (fun n : ℕ => (n : ℤ)) ⊆ h • trunc A N := by
    intro z hz
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hz
    simp only [Finset.mem_Icc] at hm
    obtain ⟨f, hfA, hfsum⟩ := hM m hm.1
    rw [Finset.mem_nsmul]
    let g : Fin h → trunc A N := fun i =>
      ⟨(f i : ℤ), (mem_trunc A N (f i : ℤ)).2
        ⟨f i, hfA i,
          (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans
            ((le_of_eq hfsum).trans hm.2), rfl⟩⟩
    refine ⟨g, ?_⟩
    change (List.ofFn fun i => (f i : ℤ)).sum = (m : ℤ)
    rw [List.ofFn_eq_map, ← Fin.sum_univ_def]
    exact_mod_cast hfsum
  have hc := Finset.card_le_card hsub
  have himg : ((Finset.Icc M N).image (fun n : ℕ => (n : ℤ))).card =
    (Finset.Icc M N).card := Finset.card_image_iff.mpr Int.ofNat_injective.injOn
  rw [himg, Nat.card_Icc] at hc
  have hh : N ≤ 2 * (h • trunc A N).card := by omega
  exact (div_le_iff₀' (by norm_num : (0 : ℝ) < 2)).2 (by exact_mod_cast hh)

end Erdos337

namespace Erdos337

/--
[trunc_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/Erdos337_ruzsa_turjanyi_solution.lean)
-/
@[path]
lemma trunc_card_le
  {A : Set ℕ}
  {N : ℕ} :
-- imply
  (trunc A N).card ≤ (A ∩ Icc 1 N).ncard + 1 := by
-- proof
  let C : Finset ℕ := (A ∩ Icc 0 N).toFinite.toFinset
  let D : Finset ℕ := (A ∩ Icc 1 N).toFinite.toFinset
  have hsub : C ⊆ D ∪ {0} := by
    intro n hn
    simp only [C, Set.Finite.mem_toFinset, Set.mem_inter_iff, mem_Icc] at hn
    simp only [Finset.mem_union, D, Set.Finite.mem_toFinset, Set.mem_inter_iff,
      mem_Icc, Finset.mem_singleton]
    by_cases hn0 : n = 0
    · exact Or.inr hn0
    · exact Or.inl ⟨hn.1, by omega, hn.2.2⟩
  calc
    _ = C.card := by
      rw [trunc]
      exact Finset.card_image_iff.mpr Int.ofNat_injective.injOn
    _ ≤ (D ∪ {0}).card := Finset.card_le_card hsub
    _ ≤ D.card + 1 := by simpa using Finset.card_union_le D {0}
    _ = _ := by
      rw [show D.card = (A ∩ Icc 1 N).ncard from
        (Set.ncard_eq_toFinset_card _ _).symm]

end Erdos337

namespace Erdos337

/--
[trunc_add_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/Erdos337_ruzsa_turjanyi_solution.lean)
-/
@[path]
lemma trunc_add_card_le
  {A : Set ℕ}
  {N : ℕ} :
-- imply
  (trunc A N + trunc A N).card ≤ ((A + A) ∩ Icc 1 (2 * N)).ncard + 1 := by
-- proof
  let Q : Finset ℕ := ((A + A) ∩ Icc 1 (2 * N)).toFinite.toFinset
  have hsub : trunc A N + trunc A N ⊆
    (Q ∪ {0}).image (fun n : ℕ => (n : ℤ)) := by
    intro z hz
    rw [Finset.mem_add] at hz
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    obtain ⟨a, ha, haN, rfl⟩ := (mem_trunc A N x).1 hx
    obtain ⟨b, hb, hbN, rfl⟩ := (mem_trunc A N y).1 hy
    apply Finset.mem_image.2
    refine ⟨a + b, ?_, by omega⟩
    simp only [Finset.mem_union, Finset.mem_singleton]
    by_cases hab : a + b = 0
    · exact Or.inr hab
    · left
      simp only [Q, Set.Finite.mem_toFinset, Set.mem_inter_iff, Set.mem_add, mem_Icc]
      exact ⟨⟨a, ha, b, hb, rfl⟩, by omega, by omega⟩
  calc
    _ ≤ ((Q ∪ {0}).image (fun n : ℕ => (n : ℤ))).card := Finset.card_le_card hsub
    _ ≤ (Q ∪ {0}).card := Finset.card_image_le
    _ ≤ Q.card + 1 := by simpa using Finset.card_union_le Q {0}
    _ = _ := by
      rw [show Q.card = ((A + A) ∩ Icc 1 (2 * N)).ncard from
        (Set.ncard_eq_toFinset_card _ _).symm]

end Erdos337

namespace Erdos337

/--
[trunc_card_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/Erdos337_ruzsa_turjanyi_solution.lean)
-/
@[path]
lemma trunc_card_ge
  {A : Set ℕ}
  {N : ℕ} :
-- imply
  (A ∩ Icc 1 N).ncard ≤ (trunc A N).card := by
-- proof
  have himg : (trunc A N).card = (A ∩ Icc 0 N).toFinite.toFinset.card := by
    rw [trunc]
    exact Finset.card_image_iff.mpr Int.ofNat_injective.injOn
  calc
    (A ∩ Icc 1 N).ncard = (A ∩ Icc 1 N).toFinite.toFinset.card :=
      Set.ncard_eq_toFinset_card _ _
    _ ≤ (A ∩ Icc 0 N).toFinite.toFinset.card := by
      apply Finset.card_le_card
      intro n hn
      have hn' : n ∈ A ∩ Icc 1 N := by simpa using hn
      have : n ∈ A ∩ Icc 0 N := ⟨hn'.1, Nat.zero_le n, hn'.2.2⟩
      simpa using this
    _ = (trunc A N).card := himg.symm

end Erdos337

namespace Erdos337

/--
[basis_denominator_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/Erdos337_ruzsa_turjanyi_solution.lean)
-/
@[path]
lemma basis_denominator_pos
  {A : Set ℕ}
  {h : ℕ}
-- given
  (hb : A.IsAsymptoticAddBasisOfOrder h) :
-- imply
  ∀ᶠ N : ℕ in atTop, 0 < (A ∩ Icc 1 N).ncard := by
-- proof
  rw [Set.isAsymptoticAddBasisOfOrder_iff_sum, Nat.cofinite_eq_atTop,
    eventually_atTop] at hb
  obtain ⟨M, hM⟩ := hb
  filter_upwards [eventually_ge_atTop (max M 1)] with N hN
  obtain ⟨f, hf, hsum⟩ := hM N (le_trans (le_max_left _ _) hN)
  rw [Set.ncard_pos]
  have hsne : (∑ i, f i) ≠ 0 := by omega
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsne
  exact ⟨f i, hf i, by omega,
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans (by omega)⟩

end Erdos337

namespace Erdos337

/--
[pluennecke_real](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/Erdos337_ruzsa_turjanyi_solution.lean)
-/
@[path]
lemma pluennecke_real
  {h : ℕ}
  {C : Finset ℤ}
-- given
  (hC : C.Nonempty) :
-- imply
  ((h • C).card : ℝ) ≤ (((C + C).card : ℝ) / (C.card : ℝ)) ^ h * C.card := by
-- proof
  have hp := Finset.pluennecke_ruzsa_inequality_nsmul_add hC C h
  have hp' : ((h • C).card : ℚ) ≤
    (((C + C).card : ℚ) / (C.card : ℚ)) ^ h * C.card := NNRat.coe_le_coe.2 hp
  have hr := (Rat.cast_le (K := ℝ)).2 hp'
  push_cast at hr
  exact hr

end Erdos337

namespace Erdos337

/--
[erdos_337.variants.ruzsa_turjanyi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/Erdos337_ruzsa_turjanyi_solution.lean)
-/
@[path]
lemma erdos_337.variants.ruzsa_turjanyi
-- imply
  ∀ A : Set ℕ, A.IsAsymptoticAddBasis → (fun N : ℕ ↦ ((A ∩ Icc 1 N).ncard : ℝ)) =o[atTop] (fun N : ℕ ↦ (N : ℝ)) → Tendsto (fun N : ℕ ↦ (((A + A) ∩ Icc 1 (2 * N)).ncard : ℝ) / ((A ∩ Icc 1 N).ncard : ℝ)) atTop atTop := by
-- proof
  intro A hbasis hdensity
  obtain ⟨h, hh⟩ := hbasis
  apply tendsto_atTop.2
  intro b
  let R : ℝ := max b 0
  have hR0 : 0 ≤ R := le_max_right _ _
  have hR1 : 0 < R + 1 := by linarith
  let P : ℝ := (R + 1) ^ h
  have hP : 0 < P := pow_pos hR1 _
  let e : ℝ := 1 / (8 * P)
  have he : 0 < e := one_div_pos.mpr (mul_pos (by norm_num) hP)
  have hdens := hdensity.def he
  obtain ⟨K : ℕ, hK⟩ := exists_nat_gt (1 / e)
  have hsmall : ∀ N : ℕ, K ≤ N → 1 < e * (N : ℝ) := by
    intro N hKN
    have hKN' : (K : ℝ) ≤ N := by exact_mod_cast hKN
    have heK : 1 < e * (K : ℝ) := by
      have := mul_lt_mul_of_pos_left hK he
      field_simp [ne_of_gt he] at this
      simpa [mul_comm] using this
    exact heK.trans_le (mul_le_mul_of_nonneg_left hKN' he.le)
  filter_upwards [basis_card_le_iterated hh, basis_denominator_pos hh, hdens,
    eventually_ge_atTop (max K 4)] with N hcover hdpos hdN hN
  let d : ℝ := ((A ∩ Icc 1 N).ncard : ℝ)
  let q : ℝ := (((A + A) ∩ Icc 1 (2 * N)).ncard : ℝ)
  let c : ℝ := ((trunc A N).card : ℝ)
  let s : ℝ := ((trunc A N + trunc A N).card : ℝ)
  have hdpos' : 0 < d := by
    dsimp [d]
    exact_mod_cast hdpos
  have hdc : d ≤ c := by
    dsimp [d, c]
    exact_mod_cast trunc_card_ge A N
  have hcpos : 0 < c := hdpos'.trans_le hdc
  have hcardpos : 0 < (trunc A N).card := by
    by_contra hz
    have hz' : (trunc A N).card = 0 := Nat.eq_zero_of_not_pos hz
    simp [c, hz'] at hcpos
  have hc_one : 1 ≤ c := by
    dsimp [c]
    exact_mod_cast hcardpos
  have hc_le : c ≤ d + 1 := by
    dsimp [c, d]
    exact_mod_cast trunc_card_le A N
  have hs_le : s ≤ q + 1 := by
    dsimp [s, q]
    exact_mod_cast trunc_add_card_le A N
  have heN : 1 < e * (N : ℝ) := hsmall N (le_trans (le_max_left _ _) hN)
  have hdN' : d ≤ e * (N : ℝ) := by simpa [d] using hdN
  have hc_bound : P * c < (N : ℝ) / 2 := by
    dsimp [e] at heN hdN'
    have hPeq : (8 * P) * (1 / (8 * P)) = 1 := by
      field_simp [ne_of_gt hP]
    have : c < 2 * (1 / (8 * P)) * (N : ℝ) := by nlinarith
    have hN0 : 0 ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
    calc
      P * c < P * (2 * (1 / (8 * P)) * (N : ℝ)) :=
        mul_lt_mul_of_pos_left this hP
      _ = (N : ℝ) / 4 := by field_simp [ne_of_gt hP] <;> ring
      _ < (N : ℝ) / 2 := by
        have hfour : (4 : ℕ) ≤ N := le_trans (le_max_right _ _) hN
        have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 4) hfour)
        linarith
  have hC : (trunc A N).Nonempty := Finset.card_pos.mp hcardpos
  have hpl := pluennecke_real (h := h) (trunc A N) hC
  by_contra hbq
  have hratio : q / d < R :=
    (lt_of_not_ge hbq).trans_le (le_max_left b 0)
  have hq : q < R * d := (div_lt_iff₀ hdpos').mp hratio
  have hsratio : s / c ≤ R + 1 := by
    apply (div_le_iff₀ hcpos).2
    nlinarith [mul_le_mul_of_nonneg_left hdc hR0]
  have hpow : (s / c) ^ h ≤ P := by
    dsimp [P]
    gcongr
  have hiter : ((h • trunc A N).card : ℝ) ≤ P * c := by
    calc
      _ ≤ (s / c) ^ h * c := by simpa [s, c] using hpl
      _ ≤ P * c := mul_le_mul_of_nonneg_right hpow hcpos.le
  linarith

end Erdos337


-- created on 2026-10-23

import Mathlib
import sympy.Basic
import Structure.v1.Atlas.EllipticCurves.code.BerlekampRabin.Part2
open Polynomial Finset BerlekampRabin


namespace BerlekampRabin

/--
[phi_psi](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/BerlekampRabin.lean)
-/
@[path]
lemma phi_psi
  [Field F]
  {α β γ : F}
-- given
  (hαβ : α ≠ β)
  (hγ : γ ≠ 1) :
-- imply
  phi α β (psi α β γ) = γ := by
-- proof
  unfold phi psi
  have h1γ : (1 : F) - γ ≠ 0 := sub_ne_zero.mpr (Ne.symm hγ)
  have hβα : β - α ≠ 0 := sub_ne_zero.mpr (Ne.symm hαβ)
  have hden : β + (γ * β - α) / (1 - γ) ≠ 0 := by
    intro h
    apply hβα
    have h1 : (β + (γ * β - α) / (1 - γ)) * (1 - γ) = 0 := by rw [h, zero_mul]
    rw [add_mul, div_mul_cancel₀ _ h1γ] at h1
    linear_combination h1
  rw [div_eq_iff hden]
  field_simp
  ring

end BerlekampRabin

namespace BerlekampRabin

/--
[psi_phi](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/BerlekampRabin.lean)
-/
@[path]
lemma psi_phi
  [Field F]
  {α β δ : F}
-- given
  (hαβ : α ≠ β)
  (hβδ : β + δ ≠ 0) :
-- imply
  psi α β (phi α β δ) = δ := by
-- proof
  unfold phi psi
  have hne1 : (α + δ) / (β + δ) ≠ 1 := by
    intro h; exact hαβ (add_right_cancel (div_eq_one_iff_eq hβδ |>.mp h))
  have h1φ : 1 - (α + δ) / (β + δ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hne1)
  rw [div_eq_iff h1φ]
  field_simp
  ring

end BerlekampRabin

namespace BerlekampRabin

/--
[phi_ne_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/BerlekampRabin.lean)
-/
@[path]
lemma phi_ne_one
  [Field F]
  {α β δ : F}
-- given
  (hαβ : α ≠ β)
  (hβδ : β + δ ≠ 0) :
-- imply
  phi α β δ ≠ 1 := by
-- proof
  unfold phi
  intro h; exact hαβ (add_right_cancel (div_eq_one_iff_eq hβδ |>.mp h))

end BerlekampRabin

namespace BerlekampRabin

/--
[psi_add_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/BerlekampRabin.lean)
-/
@[path]
lemma psi_add_ne_zero
  [Field F]
  {α β γ : F}
-- given
  (hαβ : α ≠ β)
  (hγ : γ ≠ 1) :
-- imply
  β + psi α β γ ≠ 0 := by
-- proof
  unfold psi
  intro h
  have h1γ : (1 : F) - γ ≠ 0 := sub_ne_zero.mpr (Ne.symm hγ)
  have : (β + (γ * β - α) / (1 - γ)) * (1 - γ) = 0 := by rw [h, zero_mul]
  rw [add_mul, div_mul_cancel₀ _ h1γ] at this
  exact (sub_ne_zero.mpr (Ne.symm hαβ)) (by linear_combination this)

end BerlekampRabin

namespace BerlekampRabin

/--
[card_pow_eq_const_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/BerlekampRabin.lean)
-/
@[path]
lemma card_pow_eq_const_le
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {s : ℕ}
  {c : F}
-- given
  (hs : 0 < s) :
-- imply
  (Finset.univ.filter (fun x : F => x ^ s = c)).card ≤ s := by
-- proof
  have hp : (X ^ s - C c : F[X]) ≠ 0 := by
    intro h; have := congr_arg natDegree h
    rw [natDegree_X_pow_sub_C, natDegree_zero] at this; omega
  have hinc : Finset.univ.filter (fun x : F => x ^ s = c) ⊆
    (X ^ s - C c : F[X]).roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, mem_roots hp, IsRoot.def, eval_sub, eval_pow, eval_X, eval_C,
      sub_eq_zero]
    exact (mem_filter.mp hx).2
  calc (Finset.univ.filter (fun x : F => x ^ s = c)).card
    ≤ (X ^ s - C c : F[X]).roots.toFinset.card := card_le_card hinc
    _ ≤ (X ^ s - C c : F[X]).roots.card := Multiset.toFinset_card_le _
    _ ≤ (X ^ s - C c : F[X]).natDegree := card_roots' _
    _ = s := natDegree_X_pow_sub_C

end BerlekampRabin

namespace BerlekampRabin

/--
[card_pow_eq_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/BerlekampRabin.lean)
-/
@[path]
lemma card_pow_eq_neg_one
  [Field F]
  [Fintype F]
  [DecidableEq F]
-- given
  (hF : ringChar F ≠ 2) :
-- imply
  (Finset.univ.filter (fun x : F => x ^ (Fintype.card F / 2) = -1)).card = Fintype.card F / 2 := by
-- proof
  have hq_odd : Fintype.card F % 2 = 1 := FiniteField.odd_card_of_char_ne_two hF
  have hq_gt : 1 < Fintype.card F := Fintype.one_lt_card
  have hs_pos : 0 < Fintype.card F / 2 := Nat.div_pos (by omega) (by norm_num)
  have hone_ne : (1 : F) ≠ -1 := (Ring.neg_one_ne_one_of_char_ne_two hF).symm
  have hA_le := card_pow_eq_const_le (F := F) (Fintype.card F / 2) hs_pos 1
  have hB_le := card_pow_eq_const_le (F := F) (Fintype.card F / 2) hs_pos (-1)
  suffices h : (Finset.univ.filter (fun x : F => x ^ (Fintype.card F / 2) = 1)).card +
    (Finset.univ.filter (fun x : F => x ^ (Fintype.card F / 2) = -1)).card =
    Fintype.card F - 1 by omega
  have hAB_union : (Finset.univ.filter (fun x : F => x ^ (Fintype.card F / 2) = 1)) ∪
    (Finset.univ.filter (fun x : F => x ^ (Fintype.card F / 2) = -1)) =
    Finset.univ.erase 0 := by
    ext x
    simp only [mem_union, mem_filter, mem_univ, true_and, mem_erase, ne_eq]
    constructor
    · intro hx
      refine ⟨fun hx0 => ?_, trivial⟩
      subst hx0
      obtain h | h := hx
      · exact zero_ne_one (show (0 : F) = 1 by rwa [zero_pow hs_pos.ne'] at h)
      · exact (neg_ne_zero.mpr (one_ne_zero (α := F)))
        (show (0 : F) = -1 by rwa [zero_pow hs_pos.ne'] at h).symm
    · exact fun ⟨hne, _⟩ => FiniteField.pow_dichotomy hF hne
  have hAB_disj : Disjoint (Finset.univ.filter (fun x : F => x ^ (Fintype.card F / 2) = 1))
    (Finset.univ.filter (fun x : F => x ^ (Fintype.card F / 2) = -1)) := by
    rw [Finset.disjoint_filter]
    intro x _ h1 h2; exact hone_ne (h1 ▸ h2)
  rw [← card_union_of_disjoint hAB_disj, hAB_union, card_erase_of_mem (mem_univ 0),
    card_univ]

end BerlekampRabin

namespace BerlekampRabin

/--
[rabin_card_differentTypeSet](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/BerlekampRabin.lean)
-/
@[path]
lemma rabin_card_differentTypeSet
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {α β : F}
-- given
  (hF : ringChar F ≠ 2)
  (hαβ : α ≠ β) :
-- imply
  (differentTypeSet F α β).card = Fintype.card F / 2 := by
-- proof
  set s := Fintype.card F / 2 with hs_def
  set S := differentTypeSet F α β
  set T := Finset.univ.filter (fun γ : F => γ ^ s = -1)
  have hT_card : T.card = s := card_pow_eq_neg_one hF
  have hone_ne : (1 : F) ≠ -1 := (Ring.neg_one_ne_one_of_char_ne_two hF).symm
  have hs_pos : 0 < s := by
    have := FiniteField.odd_card_of_char_ne_two hF
    have := Fintype.one_lt_card (α := F)
    omega
  rw [← hT_card]
  apply Finset.card_bij (fun δ _ => phi α β δ)
  ·
    intro δ hδ
    simp only [S, differentTypeSet, mem_filter, mem_univ, true_and, DifferentType] at hδ
    obtain ⟨hαδ, hβδ, hne⟩ := hδ
    simp only [T, mem_filter, mem_univ, true_and]
    unfold phi
    rw [div_pow]
    obtain ha | ha <;> := FiniteField.pow_dichotomy hF hαδ
      obtain hb | hb := FiniteField.pow_dichotomy hF hβδ
    · exact absurd (ha ▸ hb.symm) hne
    · rw [ha, hb]; ring
    · rw [ha, hb]; simp [div_one]
    · exact absurd (ha ▸ hb.symm) hne
  ·
    intro δ₁ hδ₁ δ₂ hδ₂ hφ
    simp only [S, differentTypeSet, mem_filter, mem_univ, true_and, DifferentType] at hδ₁ hδ₂
    have hβδ₁ : β + δ₁ ≠ 0 := hδ₁.2.1
    have hβδ₂ : β + δ₂ ≠ 0 := hδ₂.2.1
    have h1 := psi_phi α β δ₁ hαβ hβδ₁
    have h2 := psi_phi α β δ₂ hαβ hβδ₂
    rw [← h1, ← h2, hφ]
  ·
    intro γ hγ
    simp only [T, mem_filter, mem_univ, true_and] at hγ
    have hγ_ne_1 : γ ≠ 1 := by
      intro h; rw [h, one_pow] at hγ; exact hone_ne hγ
    have hγ_ne_0 : γ ≠ 0 := by
      intro h; rw [h, zero_pow hs_pos.ne'] at hγ
      exact (neg_ne_zero.mpr (one_ne_zero (α := F))) hγ.symm
    refine ⟨psi α β γ, ?_, ?_⟩
    ·
      simp only [S, differentTypeSet, mem_filter, mem_univ, true_and, DifferentType]
      have hβψ := psi_add_ne_zero α β γ hαβ hγ_ne_1
      constructor
      ·
        intro h
        have : phi α β (psi α β γ) = 0 := by
          unfold phi; rw [h, zero_div]
        rw [phi_psi α β γ hαβ hγ_ne_1] at this
        exact hγ_ne_0 this
      constructor
      · exact hβψ
      ·
        intro heq
        have hphipsi : phi α β (psi α β γ) = γ := phi_psi α β γ hαβ hγ_ne_1
        have hrat : (α + psi α β γ) ^ s / (β + psi α β γ) ^ s = γ ^ s := by
          rw [← div_pow]
          show phi α β (psi α β γ) ^ s = γ ^ s
          rw [hphipsi]
        rw [heq, div_self (pow_ne_zero _ hβψ)] at hrat
        rw [hγ] at hrat
        exact hone_ne hrat
    ·
      exact phi_psi α β γ hαβ hγ_ne_1

end BerlekampRabin

namespace BerlekampRabin

/--
[berlekampRabinStep_root_of_g](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/BerlekampRabin.lean)
-/
@[path]
lemma berlekampRabinStep_root_of_g
  {F : Type*}
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {g : F[X]}
  {δ : F}
  {r : F}
-- given
  (hr : (berlekampRabinStep F g δ).IsRoot r) :
-- imply
  g.IsRoot r :=
-- proof
  hr.dvd (EuclideanDomain.gcd_dvd_left g _)

end BerlekampRabin

namespace BerlekampRabin

/--
[berlekampRabinInit_root_of_f](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/BerlekampRabin.lean)
-/
@[path]
lemma berlekampRabinInit_root_of_f
  {F : Type*}
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {f : F[X]}
  {r : F}
-- given
  (hr : (berlekampRabinInit F f).IsRoot r) :
-- imply
  f.IsRoot r :=
-- proof
  hr.dvd (EuclideanDomain.gcd_dvd_left f _)

end BerlekampRabin

namespace BerlekampRabin

/--
[berlekampRabinInit_root_complete](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/BerlekampRabin.lean)
-/
@[path]
lemma berlekampRabinInit_root_complete
  {F : Type*}
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {f : F[X]}
  {r : F}
-- given
  (hr : f.IsRoot r) :
-- imply
  (berlekampRabinInit F f).IsRoot r := by
-- proof
  unfold berlekampRabinInit
  have hrf : (X - C r) ∣ f := dvd_iff_isRoot.mpr hr
  have hrxq : (X - C r) ∣ (X ^ Fintype.card F - X : F[X]) := by
    rw [dvd_iff_isRoot, IsRoot.def, eval_sub, eval_pow, eval_X]
    exact sub_eq_zero.mpr (FiniteField.pow_card r)
  have hrgcd : (X - C r) ∣ EuclideanDomain.gcd f (X ^ Fintype.card F - X) :=
    EuclideanDomain.dvd_gcd hrf hrxq
  rw [IsRoot.def]
  exact dvd_iff_isRoot.mp hrgcd

end BerlekampRabin

namespace BerlekampRabin

/--
[berlekampRabinStep_shift_pow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/BerlekampRabin.lean)
-/
@[path]
lemma berlekampRabinStep_shift_pow
  {F : Type*}
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {g : F[X]}
  {δ : F}
  {r : F}
-- given
  (hr : (berlekampRabinStep F g δ).IsRoot r) :
-- imply
  (r + δ) ^ (Fintype.card F / 2) = 1 := by
-- proof
  have h2 := hr.dvd (EuclideanDomain.gcd_dvd_right g _)
  rw [IsRoot.def, eval_sub, eval_one, eval_pow, eval_add, eval_X, eval_C,
    sub_eq_zero] at h2
  exact h2

end BerlekampRabin

namespace BerlekampRabin

/--
[extractRoot_isRoot](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/BerlekampRabin.lean)
-/
@[path]
lemma extractRoot_isRoot
  {F : Type*}
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {g : F[X]}
-- given
  (hg : g.natDegree = 1)
  (hm : g.Monic) :
-- imply
  g.IsRoot (extractRoot F g) := by
-- proof
  have hlc : g.leadingCoeff = 1 := hm
  rw [extractRoot, hlc, div_one]
  rw [IsRoot.def]
  have hg_eq : g = X + C (g.coeff 0) := by
    have h1 : g.coeff 1 = 1 := by
      rw [← hlc, Polynomial.leadingCoeff]
      congr 1; omega
    ext n
    match n with
    | 0 => simp
    | 1 => simp [coeff_X, h1]
    | n + 2 =>
      have : g.coeff (n + 2) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      simp [this, coeff_X]
  rw [hg_eq]
  simp [eval_add, eval_X, eval_C]
set_option linter.unusedSectionVars false in

end BerlekampRabin

namespace BerlekampRabin

/--
[chooseFactor_root_of_g](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/BerlekampRabin.lean)
-/
@[path]
lemma chooseFactor_root_of_g
  {F : Type*}
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {r : F}
-- given
  (g h : F[X])
  (hd : h ∣ g)
  (hr : (chooseFactor F g h).IsRoot r) :
-- imply
  g.IsRoot r := by
-- proof
  unfold chooseFactor at hr
  split_ifs at hr
  · exact hr.dvd hd
  · exact hr.dvd (EuclideanDomain.div_dvd_of_dvd hd)
  · exact hr

end BerlekampRabin

namespace BerlekampRabin

/--
[sq_dvd_imp_dvd_gcd_derivative](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/BerlekampRabin.lean)
-/
@[path]
lemma sq_dvd_imp_dvd_gcd_derivative
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {g f : F[X]}
-- given
  (h : g ^ 2 ∣ f) :
-- imply
  g ∣ EuclideanDomain.gcd f (Polynomial.derivative f) := by
-- proof
  apply EuclideanDomain.dvd_gcd
  · exact dvd_trans (dvd_pow_self g (by norm_num : (2 : ℕ) ≠ 0)) h
  · have := Polynomial.pow_sub_one_dvd_derivative_of_pow_dvd h
    simpa using this

end BerlekampRabin

namespace BerlekampRabin

/--
[irreducible_sq_dvd_iff_dvd_gcd_derivative](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/BerlekampRabin.lean)
-/
@[path]
lemma irreducible_sq_dvd_iff_dvd_gcd_derivative
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {g f : F[X]}
-- given
  (hg : Irreducible g) :
-- imply
  g ^ 2 ∣ f ↔ g ∣ EuclideanDomain.gcd f (Polynomial.derivative f) := by
-- proof
  constructor
  · exact sq_dvd_imp_dvd_gcd_derivative g f
  · intro h
    have hgf : g ∣ f := dvd_trans h (EuclideanDomain.gcd_dvd_left f _)
    have hgf' : g ∣ Polynomial.derivative f :=
      dvd_trans h (EuclideanDomain.gcd_dvd_right f _)
    obtain ⟨q, hfq⟩ := hgf
    rw [hfq, derivative_mul] at hgf'
    have hgdq : g ∣ Polynomial.derivative g * q := by
      have h1 : g ∣ g * Polynomial.derivative q := dvd_mul_right g _
      rw [add_comm] at hgf'
      exact (dvd_add_right h1).mp hgf'
    have hgsep : g.Separable := PerfectField.separable_of_irreducible hg
    have hgq : g ∣ q := hgsep.dvd_of_dvd_mul_left hgdq
    rw [hfq, sq]
    exact mul_dvd_mul_left g hgq
set_option linter.unusedSectionVars false in

end BerlekampRabin

namespace BerlekampRabin

/--
[finite_field_separable_iff_squarefree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/BerlekampRabin.lean)
-/
@[path]
lemma finite_field_separable_iff_squarefree
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {f : F[X]} :
-- imply
  f.Separable ↔ Squarefree f :=
-- proof
  PerfectField.separable_iff_squarefree
set_option linter.unusedSectionVars false in

end BerlekampRabin

namespace BerlekampRabin

/--
[yunInit_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/BerlekampRabin.lean)
-/
@[path]
lemma yunInit_dvd
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {f : F[X]} :
-- imply
  EuclideanDomain.gcd f (Polynomial.derivative f) ∣ f :=
-- proof
  EuclideanDomain.gcd_dvd_left f _

end BerlekampRabin

namespace BerlekampRabin

/--
[equalDegreeSplitStep_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/BerlekampRabin.lean)
-/
@[path]
lemma equalDegreeSplitStep_dvd
  {F : Type*}
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {g u : F[X]}
  {j : ℕ} :
-- imply
  equalDegreeSplitStep F g u j ∣ g := by
-- proof
  unfold equalDegreeSplitStep
  simp only
  split_ifs <;> [exact EuclideanDomain.gcd_dvd_left g u;
    exact EuclideanDomain.gcd_dvd_left g _; exact dvd_refl g]

end BerlekampRabin

namespace BerlekampRabin

/--
[equalDegreeSplitStep_root_of_g](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/BerlekampRabin.lean)
-/
@[path]
lemma equalDegreeSplitStep_root_of_g
  {F : Type*}
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {g u : F[X]}
  {j : ℕ}
  {r : F}
-- given
  (hr : (equalDegreeSplitStep F g u j).IsRoot r) :
-- imply
  g.IsRoot r :=
-- proof
  hr.dvd (equalDegreeSplitStep_dvd F g u j)

end BerlekampRabin

namespace BerlekampRabin

/--
[distinctDegreeStep_fst_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/BerlekampRabin.lean)
-/
@[path]
lemma distinctDegreeStep_fst_dvd
  {F : Type*}
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {g : F[X]}
  {j : ℕ} :
-- imply
  (distinctDegreeStep F g j).1 ∣ g :=
-- proof
  EuclideanDomain.gcd_dvd_left g _

end BerlekampRabin


-- created on 2026-10-23

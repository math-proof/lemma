import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
import Lemma.MvPolynomial.RothHelpers
import Lemma.MvPolynomial.AbsCoeffRothTranslate.le.MulMulPow4SumRothMvL1Prod_PowMax.of.RothMvIndex
import Lemma.Fin.MapRothMvHasse.eq.RothMvHasse_Map.of.RothMvIndex
import Lemma.Fin.EvalRothTranslateM.eq.Eval_Add
import Lemma.Fin.RothMvVanishesBelow_Sub.of.RothMvIndex
import Lemma.Nat.Add_1.le.Pow2.of.Gt_0
open MathlibExt.NumberTheory.RothAuxiliary
open MvPolynomial Fin Nat Real


private lemma rothDegreeBoundOver_map_h
  {R S : Type*}
  [CommSemiring R]
  [CommSemiring S]
  {m : ℕ}
  (f : R →+* S)
  {P : MvPolynomial (Fin m) R}
  {r : Fin m → ℕ}
-- given
  (hP : rothDegreeBoundOver P r) :
-- imply
  rothDegreeBoundOver (MvPolynomial.map f P) r := by
-- proof
  intro k hk h
  exact hP k (MvPolynomial.support_map_subset f P hk) h

private lemma rothMvHasse_eq_zero_of_exponent_gt_h
  {R : Type*}
  [CommSemiring R]
  {m : ℕ}
  {P : MvPolynomial (Fin m) R}
  {r : Fin m → ℕ}
-- given
  (hP : rothDegreeBoundOver P r)
  {i : RothMvIndex m}
  {h : Fin m}
  (hi : r h < i h) :
-- imply
  rothMvHasse i P = 0 := by
-- proof
  ext k
  rw [rothMvHasse_coeff_h, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  have hnot : k + i ∉ P.support := by
    intro hmem
    have := hP (k + i) hmem h
    simp only [Finsupp.add_apply] at this
    omega
  rw [MvPolynomial.notMem_support_iff.mp hnot, mul_zero]

private lemma rothDegreeBoundOver_translate_h
  {R : Type*}
  [CommRing R]
  {m : ℕ}
  {P : MvPolynomial (Fin m) R}
  {r : Fin m → ℕ}
-- given
  (hP : rothDegreeBoundOver P r)
  (x : Fin m → R) :
-- imply
  rothDegreeBoundOver (rothTranslate m x P) r := by
-- proof
  intro i hi h
  by_contra hri
  have hgt : r h < i h := Nat.lt_of_not_ge hri
  have hzero : rothMvHasse i P = 0 :=
    rothMvHasse_eq_zero_of_exponent_gt_h hP hgt
  have hcoeff := MvPolynomial.mem_support_iff.mp hi
  rw [rothTranslate_coeff_eq_eval_hasse_h, hzero, map_zero] at hcoeff
  exact hcoeff rfl

private lemma roth_box_card_h
  {m : ℕ}
  (r : Fin m → ℕ) :
  Fintype.card (RothBox r) = ∏ h, (r h + 1) := by
  simp [RothBox, Fintype.card_pi]

private lemma roth_support_card_le_box_h
  {R : Type*}
  [CommSemiring R]
  {m : ℕ}
  {P : MvPolynomial (Fin m) R}
  {r : Fin m → ℕ}
-- given
  (hP : rothDegreeBoundOver P r) :
-- imply
  P.support.card ≤ Fintype.card (RothBox r) := by
-- proof
  classical
  let f : RothMvIndex m → RothBox r := fun i h ↦
    ⟨min (i h) (r h), Nat.lt_succ_iff.mpr (min_le_right _ _)⟩
  have hinj : Set.InjOn f (P.support : Set (RothMvIndex m)) := by
    intro i hi j hj hij
    ext h
    have hihr : i h ≤ r h := hP i hi h
    have hjhr : j h ≤ r h := hP j hj h
    have heq := congrArg (fun z : RothBox r ↦ (z h : ℕ)) hij
    simpa [f, min_eq_left hihr, min_eq_left hjhr] using heq
  calc
    _ = (P.support.image f).card :=
      (Finset.card_image_iff.mpr hinj).symm
    _ ≤ Fintype.card (RothBox r) := by
      simpa using Finset.card_le_univ (P.support.image f)

/--
[roth_taylor_hasse_upper_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  (P : MvPolynomial (Fin m) ℤ)
  (x y : Fin m → ℝ)
  (r : Fin m → ℕ)
  (i : RothMvIndex m)
  (T a Q : ℝ)
-- given
  (hr : ∀ h, 0 < r h)
  (hP : rothDegreeBound P r)
  (hvan : rothMvVanishesBelow
    (MvPolynomial.map (algebraMap ℤ ℝ) P) x r T)
  (ha : 0 ≤ a)
  (hQ : 1 ≤ Q)
  (herr : ∀ l : RothMvIndex m,
    ∏ h, |y h - x h| ^ l h ≤
      Real.rpow Q (-a * rothMvWeight r l)) :
-- imply
  |MvPolynomial.eval₂ (algebraMap ℤ ℝ) y (rothMvHasse i P)| ≤
    ((8 ^ (∑ h, r h) * rothMvL1 P : ℕ) : ℝ) *
      (∏ h, max 1 |x h| ^ r h) *
        Real.rpow Q (-a * (T - rothMvWeight r i)) := by
-- proof
  classical
  let PR : MvPolynomial (Fin m) ℝ := MvPolynomial.map (algebraMap ℤ ℝ) P
  let Pi : MvPolynomial (Fin m) ℝ := rothMvHasse i PR
  let z : Fin m → ℝ := fun h ↦ y h - x h
  let R := rothTranslate m x Pi
  have hPiDeg : rothDegreeBoundOver Pi r := by
    dsimp [Pi, PR]
    apply rothDegreeBoundOver_hasse_h
    exact rothDegreeBoundOver_map_h (algebraMap ℤ ℝ) (show rothDegreeBoundOver P r from hP)
  have hRDeg : rothDegreeBoundOver R r := rothDegreeBoundOver_translate_h hPiDeg x
  have hbox : Fintype.card (RothBox r) ≤ 2 ^ (∑ h, r h) := by
    rw [roth_box_card_h]
    calc
      _ ≤ ∏ h, 2 ^ r h := by
        gcongr with h
        exact Add_1.le.Pow2.of.Gt_0 (hr h)
      _ = 2 ^ (∑ h, r h) := Finset.prod_pow_eq_pow_sum Finset.univ r 2
  have hcard : R.support.card ≤ 2 ^ (∑ h, r h) :=
    (roth_support_card_le_box_h hRDeg).trans hbox
  have hshift : MvPolynomial.eval z R = MvPolynomial.eval y Pi := by
    have ht := EvalRothTranslateM.eq.Eval_Add x z Pi
    rwa [show (fun h ↦ z h + x h) = y by funext h; simp [z]] at ht
  rw [MvPolynomial.eval₂_eq_eval_map, MapRothMvHasse.eq.RothMvHasse_Map.of.RothMvIndex]
  change |MvPolynomial.eval y Pi| ≤ _
  rw [← hshift, MvPolynomial.eval_eq']
  let C : ℝ := ((4 ^ (∑ h, r h) * rothMvL1 P : ℕ) : ℝ) *
    ∏ h, max 1 |x h| ^ r h
  let E : ℝ := Real.rpow Q (-a * (T - rothMvWeight r i))
  have hterm : ∀ l ∈ R.support,
      |R.coeff l * ∏ h, z h ^ l h| ≤ C * E := by
    intro l hl
    have hcoeff : |R.coeff l| ≤ C := by
      dsimp [R, Pi, PR, C]
      exact AbsCoeffRothTranslate.le.MulMulPow4SumRothMvL1Prod_PowMax.of.RothMvIndex
        P x r hP i l
    have hweight : T - rothMvWeight r i ≤ rothMvWeight r l := by
      have hv := RothMvVanishesBelow_Sub.of.RothMvIndex hvan i
      by_contra hn
      exact (MvPolynomial.mem_support_iff.mp hl) (hv l (lt_of_not_ge hn))
    have hexp : -a * rothMvWeight r l ≤ -a * (T - rothMvWeight r i) := by
      nlinarith
    have hmonomial : |∏ h, z h ^ l h| ≤ E := by
      rw [Finset.abs_prod]
      simp only [abs_pow]
      exact (herr l).trans
        (Real.rpow_le_rpow_of_exponent_le hQ hexp)
    rw [abs_mul]
    exact mul_le_mul hcoeff hmonomial (abs_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg fun _ _ ↦ by positivity))
  calc
    _ ≤ ∑ l ∈ R.support, |R.coeff l * ∏ h, z h ^ l h| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ ∈ R.support, C * E := by
      gcongr with l hl
      exact hterm l hl
    _ = (R.support.card : ℝ) * (C * E) := by simp
    _ ≤ ((2 ^ (∑ h, r h) : ℕ) : ℝ) * (C * E) := by
      apply mul_le_mul_of_nonneg_right
      ·
        exact_mod_cast hcard
      ·
        dsimp [C, E]
        positivity
    _ = ((8 ^ (∑ h, r h) * rothMvL1 P : ℕ) : ℝ) *
        (∏ h, max 1 |x h| ^ r h) *
          Real.rpow Q (-a * (T - rothMvWeight r i)) := by
      dsimp [C, E]
      push_cast
      have hpow : (2 : ℝ) ^ (∑ h, r h) * 4 ^ (∑ h, r h) =
          8 ^ (∑ h, r h) := by
        rw [← mul_pow]
        norm_num
      rw [← hpow]
      ring


-- created on 2026-10-21

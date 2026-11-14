import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.RothAuxiliary.Part7
import Lemma.Fin.EvalRothTranslateM.eq.Eval_Add
import Lemma.Fin.MapRothMvHasse.eq.RothMvHasse_Map.of.RothMvIndex
import Lemma.Fin.RothMvVanishesBelow_Sub.of.RothMvIndex
import Lemma.Nat.Add_1.le.Pow2.of.Gt_0
import Lemma.Real.RothFiniteDeps
open MathlibExt.NumberTheory.RothAuxiliary
open MvPolynomial Fin Nat Real



private lemma roth_abs_eval₂_le_l1_h {m : ℕ} (P : MvPolynomial (Fin m) ℤ)
    (x : Fin m → ℝ) (r : Fin m → ℕ) (hP : rothDegreeBound P r) :
    |MvPolynomial.eval₂ (algebraMap ℤ ℝ) x P| ≤
      (rothMvL1 P : ℝ) * ∏ h, max 1 |x h| ^ r h := by
  classical
  rw [MvPolynomial.eval₂_eq']
  calc
    |∑ d ∈ P.support,
        (algebraMap ℤ ℝ) (P.coeff d) * ∏ h, x h ^ d h| ≤
        ∑ d ∈ P.support,
          |(algebraMap ℤ ℝ) (P.coeff d) * ∏ h, x h ^ d h| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ P.support,
          ((P.coeff d).natAbs : ℝ) * ∏ h, max 1 |x h| ^ r h := by
      gcongr with d hd
      rw [abs_mul, Finset.abs_prod]
      have hcoeff : |(algebraMap ℤ ℝ) (P.coeff d)| = ((P.coeff d).natAbs : ℝ) := by
        rw [algebraMap_int_eq, Int.coe_castRingHom]
        norm_num
      rw [hcoeff]
      gcongr with h
      rw [abs_pow]
      exact (pow_le_pow_left₀ (abs_nonneg _) (le_max_right 1 |x h|) _).trans
        (pow_le_pow_right₀ (le_max_left _ _) (hP d hd h))
    _ = (rothMvL1 P : ℝ) * ∏ h, max 1 |x h| ^ r h := by
      rw [← Finset.sum_mul]
      unfold rothMvL1 rothFinsuppL1
      rw [← MvPolynomial.finsupp_support_eq_support]
      norm_cast


private lemma AbsCoeffRothTranslate.le.MulMulPow4SumRothMvL1Prod_PowMax.of.RothMvIndex
  {m : ℕ}
  (P : MvPolynomial (Fin m) ℤ) (x : Fin m → ℝ) (r : Fin m → ℕ)
  (hP : rothDegreeBound P r) (i l : RothMvIndex m) :
  |(rothTranslate m x
      (rothMvHasse i (MvPolynomial.map (algebraMap ℤ ℝ) P))).coeff l| ≤
    ((4 ^ (∑ h, r h) * rothMvL1 P : ℕ) : ℝ) *
      ∏ h, max 1 |x h| ^ r h := by
  let Pi := rothMvHasse i P
  let Pil := rothMvHasse l Pi
  have hPiDeg : rothDegreeBound Pi r :=
    rothDegreeBoundOver_hasse_h (show rothDegreeBoundOver P r from hP) i
  have hPilDeg : rothDegreeBound Pil r :=
    rothDegreeBoundOver_hasse_h (show rothDegreeBoundOver Pi r from hPiDeg) l
  have hPiL1 : rothMvL1 Pi ≤ 2 ^ (∑ h, r h) * rothMvL1 P :=
    rothMvL1_hasse_le_h P i r hP
  have hPilL1 : rothMvL1 Pil ≤ 4 ^ (∑ h, r h) * rothMvL1 P := calc
    _ ≤ 2 ^ (∑ h, r h) * rothMvL1 Pi :=
      rothMvL1_hasse_le_h Pi l r hPiDeg
    _ ≤ 2 ^ (∑ h, r h) * (2 ^ (∑ h, r h) * rothMvL1 P) := by
      gcongr
    _ = 4 ^ (∑ h, r h) * rothMvL1 P := by
      rw [← mul_assoc, ← mul_pow]
      norm_num
  rw [rothTranslate_coeff_eq_eval_hasse_h]
  have hmap :
    rothMvHasse l
      (rothMvHasse i (MvPolynomial.map (algebraMap ℤ ℝ) P)) =
      MvPolynomial.map (algebraMap ℤ ℝ) Pil := by
    dsimp [Pil, Pi]
    rw [← rothMvHasse_map_h, ← rothMvHasse_map_h]
  rw [hmap, ← MvPolynomial.eval₂_eq_eval_map]
  calc
    _ ≤ (rothMvL1 Pil : ℝ) * ∏ h, max 1 |x h| ^ r h :=
      roth_abs_eval₂_le_l1_h Pil x r hPilDeg
    _ ≤ ((4 ^ (∑ h, r h) * rothMvL1 P : ℕ) : ℝ) *
        ∏ h, max 1 |x h| ^ r h := by
      gcongr

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
-- updated on 2026-11-13

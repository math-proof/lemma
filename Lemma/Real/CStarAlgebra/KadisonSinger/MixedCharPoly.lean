import Mathlib
import sympy.Basic
import Def.Analysis.CStarAlgebra.KadisonSinger.MixedCharPoly
open scoped BigOperators
open Polynomial
open MvPolynomial
open MathlibExt.Analysis.CStarAlgebra.KadisonSinger


namespace MathlibExt.Analysis.CStarAlgebra.KadisonSinger


namespace Matrix

/--
[detLinear_finset_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger/MixedCharPoly.lean)
-/
@[path]
private lemma detLinear_finset_sum {n ι R : Type*}
  [Fintype n] [DecidableEq n] [CommRing R]
  (B : Matrix n n R) (A : ι → Matrix n n R) (s : Finset ι) :
  detLinear B (∑ i ∈ s, A i) = ∑ i ∈ s, detLinear B (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    unfold detLinear
    simp only [Finset.sum_empty]
    apply Finset.sum_eq_zero
    intro i hi
    change det (updateRow B i (0 : n → R)) = 0
    simpa using det_updateRow_smul B i (0 : R) (fun _ ↦ 0)
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [detLinear_add, ih]

end Matrix

namespace Matrix

/--
[detLinear_sum_smul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger/MixedCharPoly.lean)
-/
@[path]
private lemma detLinear_sum_smul {n ι R : Type*}
  [Fintype n] [DecidableEq n] [Fintype ι] [CommRing R]
  (B : Matrix n n R) (a : ι → R) (A : ι → Matrix n n R) :
  detLinear B (∑ i, a i • A i) = ∑ i, a i * detLinear B (A i) := by
  rw [detLinear_finset_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact detLinear_smul B (A i) (a i)
end Matrix
namespace MathlibExt.Analysis.CStarAlgebra.KadisonSinger
open MvPolynomial


namespace MathlibExt.Analysis.CStarAlgebra.KadisonSinger

/--
[ksMixedDifferential_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger/MixedCharPoly.lean)
-/
@[path]
private lemma ksMixedDifferential_add {σ R : Type*} [CommRing R]
  (is : List σ) (p q : MvPolynomial σ R) :
  mixedDifferential is (p + q) = mixedDifferential is p + mixedDifferential is q := by
  induction is generalizing p q with
  | nil => rfl
  | cons i is ih =>
    rw [mixedDifferential_cons, mixedDifferential_cons, mixedDifferential_cons, map_add]
    rw [show p + q - (pderiv i p + pderiv i q) =
      (p - pderiv i p) + (q - pderiv i q) by abel]
    exact ih _ _

end MathlibExt.Analysis.CStarAlgebra.KadisonSinger

namespace MathlibExt.Analysis.CStarAlgebra.KadisonSinger

/--
[ksMixedDifferential_smul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger/MixedCharPoly.lean)
-/
@[path]
private lemma ksMixedDifferential_smul {σ : Type*}
  (is : List σ) (a : ℂ) (p : MvPolynomial σ ℂ) :
  mixedDifferential is (a • p) = a • mixedDifferential is p := by
  induction is generalizing p with
  | nil => rfl
  | cons i is ih =>
    rw [mixedDifferential_cons, mixedDifferential_cons]
    have hpd : pderiv i (a • p) = a • pderiv i p := by
      rw [MvPolynomial.smul_eq_C_mul, Derivation.leibniz, derivation_C]
      simp [Algebra.smul_def]
    rw [hpd, ← smul_sub, ih]

end MathlibExt.Analysis.CStarAlgebra.KadisonSinger

namespace MathlibExt.Analysis.CStarAlgebra.KadisonSinger

/--
[ksMixedDifferential_sum_smul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger/MixedCharPoly.lean)
-/
@[path]
private lemma ksMixedDifferential_sum_smul {σ ι : Type*}
  [Fintype ι] (is : List σ) (a : ι → ℂ)
  (p : ι → MvPolynomial σ ℂ) :
  mixedDifferential is (∑ i, a i • p i) = ∑ i, a i • mixedDifferential is (p i) := by
  classical
  have hfinset (s : Finset ι) :
    mixedDifferential is (∑ i ∈ s, a i • p i) =
      ∑ i ∈ s, a i • mixedDifferential is (p i) := by
    induction s using Finset.induction_on with
    | empty =>
      have hzero : mixedDifferential is (0 : MvPolynomial σ ℂ) = 0 := by
        induction is with
        | nil => rfl
        | cons j js ih => rw [mixedDifferential_cons]; simp [ih]
      simpa using hzero
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [ksMixedDifferential_add, ksMixedDifferential_smul, ih]
  simpa using hfinset Finset.univ

end MathlibExt.Analysis.CStarAlgebra.KadisonSinger

namespace MathlibExt.Analysis.CStarAlgebra.KadisonSinger

/--
[eval_mixedDetPolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger/MixedCharPoly.lean)
-/
@[path]
lemma eval_mixedDetPolynomial
  [Fintype d] [DecidableEq d]
  {m : ℕ}
  {A : Fin m → Matrix d d ℂ}
  {z : Unit ⊕ Fin m → ℂ} :
-- imply
  MvPolynomial.eval z (mixedDetPolynomial A) =
    Matrix.det (Matrix.scalar d (z (Sum.inl ())) + ∑ i, z (Sum.inr i) • A i) := by
-- proof
  rw [mixedDetPolynomial, RingHom.map_det]
  congr 1
  ext j k
  simp only [Matrix.add_apply, map_add, Matrix.sum_apply, map_sum, Matrix.smul_apply]
  by_cases hjk : j = k <;> simp [Matrix.scalar_apply, hjk]

end MathlibExt.Analysis.CStarAlgebra.KadisonSinger

namespace MathlibExt.Analysis.CStarAlgebra.KadisonSinger

/--
[ksSpecializeAt_pderiv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger/MixedCharPoly.lean)
-/
@[path]
private lemma ksSpecializeAt_pderiv {σ R : Type*} [CommRing R]
  (i : σ) [DecidableEq σ] (x : σ → R) (p : MvPolynomial σ R) :
  ksSpecializeAt i x (pderiv i p) = Polynomial.derivative (ksSpecializeAt i x p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [ksSpecializeAt]
  | add p q hp hq =>
    simp only [ksSpecializeAt] at hp hq ⊢
    simp only [map_add]
    rw [hp, hq]
  | mul_X p j hp =>
    simp only [ksSpecializeAt] at hp ⊢
    by_cases hji : j = i
    · subst j
      simp only [pderiv_mul, pderiv_X_self, mul_one, map_add, map_mul, eval₂Hom_X',
        Polynomial.derivative_mul]
      rw [hp]
      simp
    · simp only [pderiv_mul, pderiv_X_of_ne hji, mul_zero, add_zero, map_mul,
      eval₂Hom_X', Polynomial.derivative_mul, mul_zero, add_zero]
      simp only [hji]
      rw [hp]
      simp

end MathlibExt.Analysis.CStarAlgebra.KadisonSinger

namespace MathlibExt.Analysis.CStarAlgebra.KadisonSinger

/--
[ksEval_specializeAt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger/MixedCharPoly.lean)
-/
@[path]
private lemma ksEval_specializeAt {σ R : Type*} [CommRing R]
  (i : σ) [DecidableEq σ] (x : σ → R) (t : R) (p : MvPolynomial σ R) :
  Polynomial.eval t (ksSpecializeAt i x p) =
    MvPolynomial.eval (Function.update x i t) p := by
  change (Polynomial.evalRingHom t)
    ((eval₂Hom Polynomial.C (fun j ↦ if j = i then Polynomial.X else Polynomial.C (x j))) p) = _
  change ((Polynomial.evalRingHom t).comp
    (eval₂Hom Polynomial.C (fun j ↦ if j = i then Polynomial.X else Polynomial.C (x j)))) p = _
  rw [show (Polynomial.evalRingHom t).comp
    (eval₂Hom Polynomial.C (fun j ↦ if j = i then Polynomial.X else Polynomial.C (x j))) =
    MvPolynomial.eval (Function.update x i t) by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro j
      by_cases hji : j = i
      · subst j
        simp
      · simp [hji, Function.update_of_ne]]

end MathlibExt.Analysis.CStarAlgebra.KadisonSinger

namespace MathlibExt.Analysis.CStarAlgebra.KadisonSinger

/--
[ksMixedDet_update_matrix](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger/MixedCharPoly.lean)
-/
@[path]
private lemma ksMixedDet_update_matrix {m : ℕ} {d : Type*} [Fintype d] [DecidableEq d]
  (A : Fin m → Matrix d d ℂ) (i : Fin m) (z : Unit ⊕ Fin m → ℂ) (t : ℂ) :
  Matrix.scalar d ((Function.update z (Sum.inr i) t) (Sum.inl ())) +
    ∑ j, (Function.update z (Sum.inr i) t) (Sum.inr j) • A j =
    (Matrix.scalar d (z (Sum.inl ())) +
      ∑ j ∈ Finset.univ.erase i, z (Sum.inr j) • A j) + t • A i := by
  rw [show (Function.update z (Sum.inr i) t) (Sum.inl ()) = z (Sum.inl ()) by
    rw [Function.update_of_ne]
    exact Sum.inl_ne_inr]
  rw [← Finset.add_sum_erase Finset.univ
    (fun j ↦ (Function.update z (Sum.inr i) t) (Sum.inr j) • A j)
    (Finset.mem_univ i)]
  have hi : (Function.update z (Sum.inr i) t) (Sum.inr i) = t := Function.update_self _ _ _
  rw [hi]
  have hsum :
    ∑ j ∈ Finset.univ.erase i, (Function.update z (Sum.inr i) t) (Sum.inr j) • A j =
      ∑ j ∈ Finset.univ.erase i, z (Sum.inr j) • A j := by
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    rw [Function.update_of_ne]
    exact Sum.inr_injective.ne hji
  rw [hsum]
  abel

end MathlibExt.Analysis.CStarAlgebra.KadisonSinger

namespace MathlibExt.Analysis.CStarAlgebra.KadisonSinger

/--
[mixedDetPolynomial_pderiv_sq_eq_zero_of_eq_vecMulVec](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger/MixedCharPoly.lean)
-/
@[path]
lemma mixedDetPolynomial_pderiv_sq_eq_zero_of_eq_vecMulVec
  [Fintype d] [DecidableEq d]
  {m : ℕ}
  {A : Fin m → Matrix d d ℂ}
  {i : Fin m}
  {u v : d → ℂ}
-- given
  (hi : A i = Matrix.vecMulVec u v) :
-- imply
  pderiv (Sum.inr i) (pderiv (Sum.inr i) (mixedDetPolynomial A)) = 0 := by
-- proof
  apply MvPolynomial.funext
  intro z
  let B : Matrix d d ℂ := Matrix.scalar d (z (Sum.inl ())) +
    ∑ j ∈ Finset.univ.erase i, z (Sum.inr j) • A j
  let q := ksSpecializeAt (Sum.inr i) z (mixedDetPolynomial A)
  have hq : q = Polynomial.C (Matrix.det B) + Polynomial.X *
    Polynomial.C (Matrix.det (B + Matrix.vecMulVec u v) - Matrix.det B) := by
    apply Polynomial.funext
    intro t
    rw [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_C]
    dsimp only [q]
    rw [ksEval_specializeAt, eval_mixedDetPolynomial, ksMixedDet_update_matrix]
    rw [hi, Matrix.det_add_smul_vecMulVec]
  have hqdd : Polynomial.derivative (Polynomial.derivative q) = 0 := by
    rw [hq]
    simp
  have hs : ksSpecializeAt (Sum.inr i) z
    (pderiv (Sum.inr i) (pderiv (Sum.inr i) (mixedDetPolynomial A))) = 0 := by
    rw [ksSpecializeAt_pderiv, ksSpecializeAt_pderiv]
    simpa only [q] using hqdd
  have heval := congrArg (Polynomial.eval (z (Sum.inr i))) hs
  rw [ksEval_specializeAt] at heval
  simpa using heval

end MathlibExt.Analysis.CStarAlgebra.KadisonSinger

namespace MathlibExt.Analysis.CStarAlgebra.KadisonSinger

/--
[ksAgreeAtZero_pderiv_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger/MixedCharPoly.lean)
-/
@[path]
private lemma ksAgreeAtZero_pderiv_of_ne {σ : Type*} [DecidableEq σ]
  {i j : σ} {p q : MvPolynomial σ ℂ} (hji : j ≠ i)
  (h : ksAgreeAtZero i p q) : ksAgreeAtZero i (pderiv j p) (pderiv j q) := by
  intro z
  let x := Function.update z i 0
  have hspecial : ksSpecializeAt j x p = ksSpecializeAt j x q := by
    apply Polynomial.funext
    intro t
    rw [ksEval_specializeAt, ksEval_specializeAt]
    rw [Function.update_comm hji.symm]
    exact h (Function.update z j t)
  calc
    MvPolynomial.eval x (pderiv j p) =
      (ksSpecializeAt j x (pderiv j p)).eval (x j) := by
      rw [ksEval_specializeAt]
      simp
    _ = (ksSpecializeAt j x p).derivative.eval (x j) := by
      rw [ksSpecializeAt_pderiv]
    _ = (ksSpecializeAt j x q).derivative.eval (x j) := by rw [hspecial]
    _ = (ksSpecializeAt j x (pderiv j q)).eval (x j) := by
      rw [ksSpecializeAt_pderiv]
    _ = MvPolynomial.eval x (pderiv j q) := by
      rw [ksEval_specializeAt]
      simp

end MathlibExt.Analysis.CStarAlgebra.KadisonSinger

namespace MathlibExt.Analysis.CStarAlgebra.KadisonSinger

/--
[ksAgreeAtZero_mixedDifferential](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger/MixedCharPoly.lean)
-/
@[path]
private lemma ksAgreeAtZero_mixedDifferential {σ : Type*} [DecidableEq σ]
  {i : σ} {p q : MvPolynomial σ ℂ} (is : List σ) (hi : i ∉ is)
  (h : ksAgreeAtZero i p q) :
  ksAgreeAtZero i (mixedDifferential is p) (mixedDifferential is q) := by
  induction is generalizing p q with
  | nil => exact h
  | cons j js ih =>
    rw [List.mem_cons, not_or] at hi
    rw [mixedDifferential_cons, mixedDifferential_cons]
    apply ih hi.2
    intro z
    have hderiv :
      MvPolynomial.eval (Function.update z i 0) (pderiv j p) =
        MvPolynomial.eval (Function.update z i 0) (pderiv j q) :=
      ksAgreeAtZero_pderiv_of_ne (i := i) (j := j) (p := p) (q := q)
        (Ne.symm hi.1) h z
    rw [map_sub, map_sub, h z, hderiv]

end MathlibExt.Analysis.CStarAlgebra.KadisonSinger

namespace MathlibExt.Analysis.CStarAlgebra.KadisonSinger

/--
[ksEval_one_sub_pderiv_mixedDetPolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger/MixedCharPoly.lean)
-/
@[path]
private lemma ksEval_one_sub_pderiv_mixedDetPolynomial
  {m : ℕ} {d : Type*} [Fintype d] [DecidableEq d]
  (A : Fin m → Matrix d d ℂ) (i : Fin m) (z : Unit ⊕ Fin m → ℂ) :
  MvPolynomial.eval (Function.update z (Sum.inr i) 0)
    (mixedDetPolynomial A - pderiv (Sum.inr i) (mixedDetPolynomial A)) =
    Matrix.det (ksMixedDetBaseMatrix A i z) -
      Matrix.detLinear (ksMixedDetBaseMatrix A i z) (A i) := by
  let B := ksMixedDetBaseMatrix A i z
  let q := ksSpecializeAt (Sum.inr i) z (mixedDetPolynomial A)
  have hq : q = Matrix.det
    (B.map Polynomial.C + (Polynomial.X : Polynomial ℂ) • (A i).map Polynomial.C) := by
    apply Polynomial.funext
    intro t
    dsimp only [q]
    rw [ksEval_specializeAt, eval_mixedDetPolynomial, ksMixedDet_update_matrix]
    symm
    change (Polynomial.evalRingHom t)
      (Matrix.det (B.map Polynomial.C +
        (Polynomial.X : Polynomial ℂ) • (A i).map Polynomial.C)) = _
    rw [RingHom.map_det]
    congr 1
    ext a b
    simp [B, ksMixedDetBaseMatrix]
    ring
  have hvalue :
    MvPolynomial.eval (Function.update z (Sum.inr i) 0) (mixedDetPolynomial A) =
      Matrix.det B := by
    rw [eval_mixedDetPolynomial, ksMixedDet_update_matrix]
    simp [B, ksMixedDetBaseMatrix]
  have hderiv :
    MvPolynomial.eval (Function.update z (Sum.inr i) 0)
      (pderiv (Sum.inr i) (mixedDetPolynomial A)) =
      Matrix.detLinear B (A i) := by
    calc
      MvPolynomial.eval (Function.update z (Sum.inr i) 0)
        (pderiv (Sum.inr i) (mixedDetPolynomial A)) =
        (ksSpecializeAt (Sum.inr i) z
          (pderiv (Sum.inr i) (mixedDetPolynomial A))).eval 0 := by
        rw [ksEval_specializeAt]
      _ = q.derivative.eval 0 := by rw [ksSpecializeAt_pderiv]
      _ = q.coeff 1 := by
        rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
        simp
      _ = Matrix.detLinear B (A i) := by
        rw [hq]
        exact Matrix.coeff_one_det_add_X_smul B (A i)
  rw [map_sub, hvalue, hderiv]

end MathlibExt.Analysis.CStarAlgebra.KadisonSinger

namespace MathlibExt.Analysis.CStarAlgebra.KadisonSinger

/--
[ksMixedDetBaseMatrix_update](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger/MixedCharPoly.lean)
-/
@[path]
private lemma ksMixedDetBaseMatrix_update
  {m : ℕ} {d : Type*} [Fintype d] [DecidableEq d]
  (A : Fin m → Matrix d d ℂ) (i : Fin m) (C : Matrix d d ℂ)
  (z : Unit ⊕ Fin m → ℂ) :
  ksMixedDetBaseMatrix (Function.update A i C) i z = ksMixedDetBaseMatrix A i z := by
  unfold ksMixedDetBaseMatrix
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

end MathlibExt.Analysis.CStarAlgebra.KadisonSinger

namespace MathlibExt.Analysis.CStarAlgebra.KadisonSinger

/--
[ksAgreeAtZero_one_sub_pderiv_update_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger/MixedCharPoly.lean)
-/
@[path]
private lemma ksAgreeAtZero_one_sub_pderiv_update_sum
  {m : ℕ} {d ι : Type*} [Fintype d] [DecidableEq d] [Fintype ι]
  (A : Fin m → Matrix d d ℂ) (i : Fin m) (w : ι → ℝ)
  (C : ι → Matrix d d ℂ) (hsum : ∑ a, w a = 1) :
  ksAgreeAtZero (Sum.inr i)
    (mixedDetPolynomial (Function.update A i (∑ a, (w a : ℂ) • C a)) -
      pderiv (Sum.inr i)
        (mixedDetPolynomial (Function.update A i (∑ a, (w a : ℂ) • C a))))
    (∑ a, (w a : ℂ) •
      (mixedDetPolynomial (Function.update A i (C a)) -
        pderiv (Sum.inr i) (mixedDetPolynomial (Function.update A i (C a))))) := by
  classical
  intro z
  rw [ksEval_one_sub_pderiv_mixedDetPolynomial]
  rw [map_sum]
  have hterm (a : ι) :
    MvPolynomial.eval (Function.update z (Sum.inr i) 0)
      ((w a : ℂ) •
        (mixedDetPolynomial (Function.update A i (C a)) -
          pderiv (Sum.inr i) (mixedDetPolynomial (Function.update A i (C a))))) =
      (w a : ℂ) *
        (Matrix.det (ksMixedDetBaseMatrix (Function.update A i (C a)) i z) -
          Matrix.detLinear (ksMixedDetBaseMatrix (Function.update A i (C a)) i z)
            (Function.update A i (C a) i)) := by
    rw [MvPolynomial.smul_eq_C_mul, map_mul, eval_C,
      ksEval_one_sub_pderiv_mixedDetPolynomial]
  simp_rw [hterm]
  simp_rw [ksMixedDetBaseMatrix_update]
  simp_rw [Function.update_self]
  rw [Matrix.detLinear_sum_smul]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  have hsumC : (∑ a, (w a : ℂ)) = 1 := by
    calc
      (∑ a, (w a : ℂ)) = Complex.ofRealHom (∑ a, w a) :=
        (map_sum Complex.ofRealHom w Finset.univ).symm
      _ = 1 := by rw [hsum]; simp
  rw [hsumC, one_mul]

end MathlibExt.Analysis.CStarAlgebra.KadisonSinger

namespace MathlibExt.Analysis.CStarAlgebra.KadisonSinger

/--
[ksEval_mixedCharacteristicPolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger/MixedCharPoly.lean)
-/
@[path]
private lemma ksEval_mixedCharacteristicPolynomial
  {m : ℕ} {d : Type*} [Fintype d] [DecidableEq d]
  (A : Fin m → Matrix d d ℂ) (x : ℂ) :
  Polynomial.eval x (mixedCharacteristicPolynomial A) =
    MvPolynomial.eval (Sum.elim (fun _ ↦ x) (fun _ ↦ 0))
      (mixedDifferential ((List.finRange m).map Sum.inr) (mixedDetPolynomial A)) := by
  let q := mixedDifferential ((List.finRange m).map Sum.inr) (mixedDetPolynomial A)
  change (Polynomial.evalRingHom x)
    ((eval₂Hom Polynomial.C (Sum.elim (fun _ ↦ Polynomial.X) (fun _ ↦ 0))) q) = _
  change ((Polynomial.evalRingHom x).comp
    (eval₂Hom Polynomial.C (Sum.elim (fun _ ↦ Polynomial.X) (fun _ ↦ 0)))) q = _
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro a
    simp
  · intro j
    obtain u | i := j
    · cases u
      simp
    · simp

end MathlibExt.Analysis.CStarAlgebra.KadisonSinger

namespace MathlibExt.Analysis.CStarAlgebra.KadisonSinger

/--
[ksEval_neg_one_eq_eval_zero_sub_derivative](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger/MixedCharPoly.lean)
-/
@[path]
private lemma ksEval_neg_one_eq_eval_zero_sub_derivative (q : Polynomial ℂ)
  (h : Polynomial.derivative (Polynomial.derivative q) = 0) :
  q.eval (-1) = q.eval 0 - q.derivative.eval 0 := by
  have hd : q.derivative.natDegree = 0 := Polynomial.derivative_eq_zero.mp h
  have hn : q.natDegree ≤ 1 := by
    rw [Polynomial.natDegree_derivative] at hd
    omega
  rw [Polynomial.eq_X_add_C_of_degree_le_one
    (Polynomial.degree_le_of_natDegree_le hn)]
  simp
  ring

end MathlibExt.Analysis.CStarAlgebra.KadisonSinger

namespace MathlibExt.Analysis.CStarAlgebra.KadisonSinger

/--
[ksEval_one_sub_pderiv_zero_eq_eval_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger/MixedCharPoly.lean)
-/
@[path]
private lemma ksEval_one_sub_pderiv_zero_eq_eval_neg_one
  {σ : Type*} [DecidableEq σ] (i : σ) (x : σ → ℂ) (p : MvPolynomial σ ℂ)
  (h : pderiv i (pderiv i p) = 0) :
  MvPolynomial.eval (Function.update x i 0) (p - pderiv i p) =
    MvPolynomial.eval (Function.update x i (-1)) p := by
  let q := ksSpecializeAt i x p
  have hqdd : Polynomial.derivative (Polynomial.derivative q) = 0 := by
    rw [← ksSpecializeAt_pderiv, ← ksSpecializeAt_pderiv, h]
    simp [ksSpecializeAt]
  calc
    MvPolynomial.eval (Function.update x i 0) (p - pderiv i p) =
      MvPolynomial.eval (Function.update x i 0) p -
        MvPolynomial.eval (Function.update x i 0) (pderiv i p) := by rw [map_sub]
    _ = q.eval 0 - (ksSpecializeAt i x (pderiv i p)).eval 0 := by
      rw [ksEval_specializeAt, ksEval_specializeAt]
    _ = q.eval 0 - q.derivative.eval 0 := by rw [ksSpecializeAt_pderiv]
    _ = q.eval (-1) := (ksEval_neg_one_eq_eval_zero_sub_derivative q hqdd).symm
    _ = MvPolynomial.eval (Function.update x i (-1)) p := ksEval_specializeAt i x (-1) p

end MathlibExt.Analysis.CStarAlgebra.KadisonSinger

namespace MathlibExt.Analysis.CStarAlgebra.KadisonSinger

/--
[ksSetVariables_cons](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger/MixedCharPoly.lean)
-/
@[path]
private lemma ksSetVariables_cons {σ : Type*} [DecidableEq σ]
  (i : σ) (is : List σ) (a : ℂ) (x : σ → ℂ) :
  ksSetVariables (i :: is) a x = Function.update (ksSetVariables is a x) i a := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [ksSetVariables]
  · simp [ksSetVariables, hji]

end MathlibExt.Analysis.CStarAlgebra.KadisonSinger

namespace MathlibExt.Analysis.CStarAlgebra.KadisonSinger

/--
[ksSetVariables_update_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger/MixedCharPoly.lean)
-/
@[path]
private lemma ksSetVariables_update_of_not_mem {σ : Type*} [DecidableEq σ]
  (i : σ) (is : List σ) (a b : ℂ) (x : σ → ℂ) (hi : i ∉ is) :
  ksSetVariables is a (Function.update x i b) =
    Function.update (ksSetVariables is a x) i b := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [ksSetVariables, hi]
  · simp [ksSetVariables, hji]

end MathlibExt.Analysis.CStarAlgebra.KadisonSinger

namespace MathlibExt.Analysis.CStarAlgebra.KadisonSinger

/--
[ksMixedDifferential_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger/MixedCharPoly.lean)
-/
@[path]
private lemma ksMixedDifferential_zero {σ : Type*} (is : List σ) :
  mixedDifferential is (0 : MvPolynomial σ ℂ) = 0 := by
  induction is with
  | nil => rfl
  | cons i is ih => rw [mixedDifferential_cons]; simp [ih]

end MathlibExt.Analysis.CStarAlgebra.KadisonSinger

namespace MathlibExt.Analysis.CStarAlgebra.KadisonSinger

/--
[ksEval_mixedDifferential_zero_eq_eval_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger/MixedCharPoly.lean)
-/
@[path]
private lemma ksEval_mixedDifferential_zero_eq_eval_neg_one
  {σ : Type*} [DecidableEq σ] (is : List σ) (p : MvPolynomial σ ℂ) (x : σ → ℂ)
  (hnodup : is.Nodup) (hmulti : ∀ i ∈ is, pderiv i (pderiv i p) = 0) :
  MvPolynomial.eval (ksSetVariables is 0 x) (mixedDifferential is p) =
    MvPolynomial.eval (ksSetVariables is (-1) x) p := by
  induction is generalizing p x with
  | nil => rfl
  | cons i is ih =>
    rw [List.nodup_cons] at hnodup
    have hperm : (i :: is).Perm (is ++ [i]) := by
      simpa using (List.perm_middle (l₁ := is) (l₂ := [])).symm
    rw [mixedDifferential_eq_of_perm hperm, mixedDifferential_append]
    rw [ksSetVariables_cons, ksSetVariables_cons]
    let q := mixedDifferential is p
    have hqi : pderiv i (pderiv i q) = 0 := by
      rw [pderiv_mixedDifferential, pderiv_mixedDifferential, hmulti i (by simp)]
      exact ksMixedDifferential_zero is
    rw [mixedDifferential_cons, mixedDifferential_nil]
    rw [ksEval_one_sub_pderiv_zero_eq_eval_neg_one i (ksSetVariables is 0 x) q hqi]
    rw [← ksSetVariables_update_of_not_mem i is 0 (-1) x hnodup.1]
    rw [ih p (Function.update x i (-1)) hnodup.2
      (fun j hj ↦ hmulti j (by simp [hj]))]
    rw [ksSetVariables_update_of_not_mem i is (-1) (-1) x hnodup.1]

end MathlibExt.Analysis.CStarAlgebra.KadisonSinger

namespace MathlibExt.Analysis.CStarAlgebra.KadisonSinger

/--
[mixedCharacteristicPolynomial_update_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger/MixedCharPoly.lean)
-/
@[path]
lemma mixedCharacteristicPolynomial_update_sum
  [Fintype d] [DecidableEq d] [Fintype ι]
  {m : ℕ}
  {A : Fin m → Matrix d d ℂ}
  {i : Fin m}
  {w : ι → ℝ}
  {C : ι → Matrix d d ℂ}
-- given
  (hsum : ∑ a, w a = 1) :
-- imply
  mixedCharacteristicPolynomial (Function.update A i (∑ a, (w a : ℂ) • C a)) =
    ∑ a, (w a : ℂ) • mixedCharacteristicPolynomial (Function.update A i (C a)) := by
-- proof
  classical
  let is : List (Unit ⊕ Fin m) := (List.finRange m).map Sum.inr
  let rest : List (Unit ⊕ Fin m) := ((List.finRange m).erase i).map Sum.inr
  have hmem : Sum.inr i ∈ is := by simp [is, List.mem_finRange]
  have hperm : is.Perm (Sum.inr i :: rest) := by
    exact (List.perm_cons_erase (show i ∈ List.finRange m by simp)).map Sum.inr
  have hnot : Sum.inr i ∉ rest := by
    simp only [rest, List.mem_map, Sum.inr.injEq, not_exists, not_and]
    intro j hj hji
    subst j
    exact (List.nodup_finRange m).not_mem_erase hj
  let Abar := Function.update A i (∑ a, (w a : ℂ) • C a)
  let Aa : ι → Fin m → Matrix d d ℂ := fun a ↦ Function.update A i (C a)
  let basebar := mixedDetPolynomial Abar - pderiv (Sum.inr i) (mixedDetPolynomial Abar)
  let base : ι → MvPolynomial (Unit ⊕ Fin m) ℂ := fun a ↦
    mixedDetPolynomial (Aa a) - pderiv (Sum.inr i) (mixedDetPolynomial (Aa a))
  change mixedCharacteristicPolynomial Abar =
    ∑ a, (w a : ℂ) • mixedCharacteristicPolynomial (Aa a)
  have hbase : ksAgreeAtZero (Sum.inr i) basebar (∑ a, (w a : ℂ) • base a) := by
    dsimp only [basebar, base, Abar, Aa]
    exact ksAgreeAtZero_one_sub_pderiv_update_sum A i w C hsum
  have hmixed := ksAgreeAtZero_mixedDifferential rest hnot hbase
  have hlinear : mixedDifferential rest (∑ a, (w a : ℂ) • base a) =
    ∑ a, (w a : ℂ) • mixedDifferential rest (base a) :=
    ksMixedDifferential_sum_smul rest (fun a ↦ (w a : ℂ)) base
  apply Polynomial.funext
  intro x
  let z : Unit ⊕ Fin m → ℂ := Sum.elim (fun _ ↦ x) (fun _ ↦ 0)
  have hzupdate : Function.update z (Sum.inr i) 0 = z := by
    funext j
    obtain u | j := j
    · cases u
      simp [z]
    · simp [z]
  have hEval : MvPolynomial.eval z (mixedDifferential rest basebar) =
    MvPolynomial.eval z
      (mixedDifferential rest (∑ a, (w a : ℂ) • base a)) := by
    have h := hmixed z
    rwa [hzupdate] at h
  have hmember (a : ι) :
    MvPolynomial.eval z (mixedDifferential rest (base a)) =
      Polynomial.eval x (mixedCharacteristicPolynomial (Aa a)) := by
    symm
    calc
      Polynomial.eval x (mixedCharacteristicPolynomial (Aa a)) =
        MvPolynomial.eval z (mixedDifferential is (mixedDetPolynomial (Aa a))) :=
        ksEval_mixedCharacteristicPolynomial (Aa a) x
      _ = MvPolynomial.eval z (mixedDifferential rest (base a)) := by
        rw [mixedDifferential_eq_of_perm hperm, mixedDifferential_cons]
  calc
    Polynomial.eval x (mixedCharacteristicPolynomial Abar) =
      MvPolynomial.eval z (mixedDifferential is (mixedDetPolynomial Abar)) :=
      ksEval_mixedCharacteristicPolynomial Abar x
    _ = MvPolynomial.eval z (mixedDifferential rest basebar) := by
      rw [mixedDifferential_eq_of_perm hperm, mixedDifferential_cons]
    _ = MvPolynomial.eval z
      (mixedDifferential rest (∑ a, (w a : ℂ) • base a)) := hEval
    _ = MvPolynomial.eval z
      (∑ a, (w a : ℂ) • mixedDifferential rest (base a)) := by rw [hlinear]
    _ = ∑ a, (w a : ℂ) *
      MvPolynomial.eval z (mixedDifferential rest (base a)) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro a ha
      rw [MvPolynomial.smul_eq_C_mul, map_mul, eval_C]
    _ = ∑ a, (w a : ℂ) *
      Polynomial.eval x (mixedCharacteristicPolynomial (Aa a)) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [hmember]
    _ = Polynomial.eval x
      (∑ a, (w a : ℂ) • mixedCharacteristicPolynomial (Aa a)) := by
      rw [Polynomial.eval_finsetSum]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Polynomial.eval_smul]
      rfl

end MathlibExt.Analysis.CStarAlgebra.KadisonSinger

namespace MathlibExt.Analysis.CStarAlgebra.KadisonSinger

/--
[mixedCharacteristicPolynomial_update_affine](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger/MixedCharPoly.lean)
-/
@[path]
lemma mixedCharacteristicPolynomial_update_affine
  [Fintype d] [DecidableEq d]
  {m : ℕ}
  {A : Fin m → Matrix d d ℂ}
  {i : Fin m}
  {B C : Matrix d d ℂ}
  {t : ℝ} :
-- imply
  mixedCharacteristicPolynomial
    (Function.update A i ((1 - (t : ℂ)) • B + (t : ℂ) • C)) =
    (1 - (t : ℂ)) • mixedCharacteristicPolynomial (Function.update A i B) +
    (t : ℂ) • mixedCharacteristicPolynomial (Function.update A i C) := by
-- proof
  let w : Fin 2 → ℝ := ![1 - t, t]
  let D : Fin 2 → Matrix d d ℂ := ![B, C]
  have hsum : ∑ a, w a = 1 := by
    simp [w]
  have h := mixedCharacteristicPolynomial_update_sum A i w D hsum
  rw [Fin.sum_univ_two, Fin.sum_univ_two] at h
  simp only [w, D, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rwa [Complex.ofReal_sub, Complex.ofReal_one] at h

end MathlibExt.Analysis.CStarAlgebra.KadisonSinger

namespace MathlibExt.Analysis.CStarAlgebra.KadisonSinger

/--
[mixedCharacteristicPolynomial_eq_charpoly_sum_of_eq_vecMulVec](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger/MixedCharPoly.lean)
-/
@[path]
lemma mixedCharacteristicPolynomial_eq_charpoly_sum_of_eq_vecMulVec
  [Fintype d] [DecidableEq d]
  {m : ℕ}
  {A : Fin m → Matrix d d ℂ}
  {u v : Fin m → d → ℂ}
-- given
  (hA : ∀ i, A i = Matrix.vecMulVec (u i) (v i)) :
-- imply
  mixedCharacteristicPolynomial A = Matrix.charpoly (∑ i, A i) := by
-- proof
  apply Polynomial.funext
  intro x
  let is : List (Unit ⊕ Fin m) := (List.finRange m).map Sum.inr
  let z : Unit ⊕ Fin m → ℂ := Sum.elim (fun _ ↦ x) (fun _ ↦ 0)
  let p := mixedDetPolynomial A
  let q := mixedDifferential is p
  have hnodup : is.Nodup := (List.nodup_finRange m).map Sum.inr_injective
  have hmulti : ∀ i ∈ is, pderiv i (pderiv i p) = 0 := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hk
    exact mixedDetPolynomial_pderiv_sq_eq_zero_of_eq_vecMulVec A i (u i) (v i) (hA i)
  have hzero : ksSetVariables is 0 z = z := by
    funext k
    obtain _ | i := k
    · simp [ksSetVariables, is, z]
    · simp [ksSetVariables, is, z, List.mem_finRange]
  have hneg : ksSetVariables is (-1) z = Sum.elim (fun _ ↦ x) (fun _ ↦ -1) := by
    funext k
    obtain _ | i := k
    · simp [ksSetVariables, is, z]
    · simp [ksSetVariables, is, z, List.mem_finRange]
  have hspecial : Polynomial.eval x (mixedCharacteristicPolynomial A) =
    MvPolynomial.eval z q := by
    change (Polynomial.evalRingHom x)
      ((eval₂Hom Polynomial.C (Sum.elim (fun _ ↦ Polynomial.X) (fun _ ↦ 0))) q) = _
    change ((Polynomial.evalRingHom x).comp
      (eval₂Hom Polynomial.C (Sum.elim (fun _ ↦ Polynomial.X) (fun _ ↦ 0)))) q = _
    congr 1
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro k
      obtain _ | i <;> simp [z] := k
  rw [hspecial]
  rw [← hzero, ksEval_mixedDifferential_zero_eq_eval_neg_one is p z hnodup hmulti, hneg]
  rw [eval_mixedDetPolynomial, Matrix.eval_charpoly]
  congr 1
  simp only [Sum.elim_inl, Sum.elim_inr, neg_smul, one_smul]
  rw [Finset.sum_neg_distrib]
  abel

end MathlibExt.Analysis.CStarAlgebra.KadisonSinger

/--
[mixedCharacteristicPolynomial_fin_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger/MixedCharPoly.lean)
-/
@[path]
lemma mixedCharacteristicPolynomial_fin_one
  {a : ℂ} :
-- imply
  mixedCharacteristicPolynomial (m := by
-- proof
  simp only [mixedCharacteristicPolynomial, mixedDifferential, mixedDetPolynomial,
    Matrix.scalar_apply, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sum_singleton, Matrix.det_unique, Matrix.add_apply, Matrix.diagonal_apply_eq,
    Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one,
    smul_eq_mul, List.finRange_succ, Nat.reduceAdd, List.finRange_zero, List.map_nil, List.map_cons,
    List.foldl_cons, map_add, pderiv_X, ne_eq, reduceCtorEq, not_false_eq_true,
    Pi.single_eq_of_ne, Derivation.leibniz, derivation_C, mul_zero, Pi.single_eq_same, mul_one,
    zero_add, List.foldl_nil, coe_eval₂Hom]
  change (eval₂Hom Polynomial.C (Sum.elim (fun _ ↦ Polynomial.X) (fun _ ↦ 0)))
    (X (Sum.inl ()) + X (Sum.inr 0) * C a - C a) = _
  rw [map_sub, map_add, map_mul]
  simp only [eval₂Hom_X', eval₂Hom_C, Sum.elim_inl, Sum.elim_inr, zero_mul, add_zero]

end MathlibExt.Analysis.CStarAlgebra.KadisonSinger


-- created on 2026-10-20
-- updated on 2026-10-23

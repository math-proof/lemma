import Mathlib
import Initialize.Tactic.Attr.Basic


private noncomputable def genMat
  {E : Type} [CommRing E] [Algebra ℝ E] [Module.Free ℝ E] [Module.Finite ℝ E]
  {m : Type} [Fintype m] [DecidableEq m] {n : ℕ} (e : Fin n → Matrix m m E) :
    Matrix m m (MvPolynomial (Fin n) E) :=
  ∑ a, (MvPolynomial.X a : MvPolynomial (Fin n) E) • (e a).map (MvPolynomial.C : E → MvPolynomial (Fin n) E)

private noncomputable def genDet
  {E : Type} [CommRing E] [Algebra ℝ E] [Module.Free ℝ E] [Module.Finite ℝ E]
  {m : Type} [Fintype m] [DecidableEq m] {n : ℕ} (e : Fin n → Matrix m m E) :
    MvPolynomial (Fin n) E :=
  (genMat e).det

private noncomputable def evE
  {E : Type} [CommRing E] [Algebra ℝ E] {n : ℕ} (c : Fin n → ℝ) :
    MvPolynomial (Fin n) E →+* E :=
  MvPolynomial.eval fun a => algebraMap ℝ E (c a)

private lemma evE_genMat
  {E : Type} [CommRing E] [Algebra ℝ E] [Module.Free ℝ E] [Module.Finite ℝ E]
  {m : Type} [Fintype m] [DecidableEq m]
  {n : ℕ} {e : Fin n → Matrix m m E} {c : Fin n → ℝ} :
-- imply
  (evE c).mapMatrix (genMat e) = ∑ a, c a • e a := by
-- proof
  ext p q
  rw [RingHom.mapMatrix_apply, Matrix.map_apply]
  simp only [genMat, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, evE, MvPolynomial.eval_X, MvPolynomial.eval_C, Algebra.smul_def]

private lemma evE_genDet
  {E : Type} [CommRing E] [Algebra ℝ E] [Module.Free ℝ E] [Module.Finite ℝ E]
  {m : Type} [Fintype m] [DecidableEq m]
  {n : ℕ} {e : Fin n → Matrix m m E} {c : Fin n → ℝ} :
-- imply
  evE c (genDet e) = (∑ a, c a • e a).det := by
-- proof
  rw [genDet, RingHom.map_det, evE_genMat]

private lemma evE_eq_sum
  {E : Type} [CommRing E] [Algebra ℝ E]
  {n : ℕ} {c : Fin n → ℝ} {D : MvPolynomial (Fin n) E} :
-- imply
  evE c D = ∑ s ∈ D.support, (s.prod fun a k => c a ^ k) • D.coeff s := by
-- proof
  conv_lhs => rw [MvPolynomial.as_sum D]
  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [evE, MvPolynomial.eval_monomial, Algebra.smul_def, mul_comm]
  congr 1
  rw [Finsupp.prod, Finsupp.prod, map_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [map_pow]

private noncomputable def lmPoly
  {E : Type} [CommRing E] [Algebra ℝ E] [Module.Free ℝ E] [Module.Finite ℝ E]
  {m : Type} [Fintype m] [DecidableEq m] {n : ℕ} (e : Fin n → Matrix m m E)
  {κ : Type} [Fintype κ] [DecidableEq κ] (b : Module.Basis κ ℝ E) :
    Matrix κ κ (MvPolynomial (Fin n) ℝ) :=
  ∑ s ∈ (genDet e).support,
    (Algebra.leftMulMatrix b ((genDet e).coeff s)).map fun r => MvPolynomial.monomial s r

private lemma eval_lmPoly
  {E : Type} [CommRing E] [Algebra ℝ E] [Module.Free ℝ E] [Module.Finite ℝ E]
  {m : Type} [Fintype m] [DecidableEq m]
  {κ : Type} [Fintype κ] [DecidableEq κ]
  {n : ℕ} {e : Fin n → Matrix m m E} {b : Module.Basis κ ℝ E} {c : Fin n → ℝ} :
-- imply
  (MvPolynomial.eval c).mapMatrix (lmPoly e b) =
    Algebra.leftMulMatrix b (evE c (genDet e)) := by
-- proof
  rw [evE_eq_sum, map_sum]
  ext k l
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, lmPoly, Matrix.sum_apply, map_sum, MvPolynomial.eval_monomial, map_smul, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  ring


/--
[Algebra_exists_mvPolynomial_forall_eval_eq_norm_det_sum_smul](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_exists_mvPolynomial_forall_eval_eq_norm_det_sum_smul.lean)
-/
@[path]
private lemma main
  {E : Type} [CommRing E] [Algebra ℝ E] [Module.Free ℝ E] [Module.Finite ℝ E]
  {m : Type} [Fintype m] [DecidableEq m]
  {n : ℕ} {e : Fin n → Matrix m m E} :
-- imply
  ∃ P : MvPolynomial (Fin n) ℝ, ∀ c : Fin n → ℝ,
    MvPolynomial.eval c P = Algebra.norm ℝ (Matrix.det (∑ a, c a • e a)) := by
-- proof
  classical
  let b := Module.Free.chooseBasis ℝ E
  refine ⟨(lmPoly e b).det, fun c => ?_⟩
  rw [RingHom.map_det, eval_lmPoly, ← Algebra.norm_eq_matrix_det b, evE_genDet]


-- created on 2026-10-13

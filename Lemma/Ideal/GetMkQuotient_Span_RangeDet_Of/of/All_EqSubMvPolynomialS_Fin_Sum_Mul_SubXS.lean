import Mathlib
import sympy.Basic
set_option maxHeartbeats 1600000
open scoped TensorProduct


private lemma adjugate_mulVec_mulVec
  {n : Type u} [Fintype n] [DecidableEq n]
  [CommRing S]
  (A : Matrix n n S) (v : n → S) :
  A.adjugate.mulVec (A.mulVec v) = A.det • v := by
  rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul]
  ext i
  simp [Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.one_apply, Finset.sum_ite_eq, ite_mul]

private lemma map_det_mul_map_eq_zero
  [CommRing R] [CommRing P] [Algebra R P] [Semiring B] [Algebra R B]
  (π : P ⊗[R] P →ₐ[R] B) {m : ℕ} (x f : Fin m → P) (a : Fin m → Fin m → P ⊗[R] P)
-- given
  (ha : ∀ i, f i ⊗ₜ[R] (1 : P) - (1 : P) ⊗ₜ[R] f i =
    ∑ j, a i j * (x j ⊗ₜ[R] 1 - 1 ⊗ₜ[R] x j))
  (hf : ∀ i, π (f i ⊗ₜ[R] (1 : P) - (1 : P) ⊗ₜ[R] f i) = 0)
  (j : Fin m) :
-- imply
  π (Matrix.det (Matrix.of a)) * π (x j ⊗ₜ[R] 1 - 1 ⊗ₜ[R] x j) = 0 := by
-- proof
  classical
  have hmat : (Matrix.of a).mulVec (fun j => x j ⊗ₜ[R] (1 : P) - 1 ⊗ₜ[R] x j) =
      fun i => f i ⊗ₜ[R] 1 - 1 ⊗ₜ[R] f i := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
    apply (ha i).symm
  have hcramer : Matrix.det (Matrix.of a) * (x j ⊗ₜ[R] (1 : P) - 1 ⊗ₜ[R] x j) =
      ∑ i, (Matrix.of a).adjugate j i * (f i ⊗ₜ[R] 1 - 1 ⊗ₜ[R] f i) := by
    have h := congrArg (fun v => v j)
      (adjugate_mulVec_mulVec (Matrix.of a) (fun j => x j ⊗ₜ[R] (1 : P) - 1 ⊗ₜ[R] x j))
    simp only [Pi.smul_apply, smul_eq_mul] at h
    rw [← h, hmat]
    rfl
  rw [← map_mul, hcramer, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_mul, hf, mul_zero]

private lemma balanced_of_adjoin
  [CommRing R] [CommRing A] [Algebra R A]
  (Δ : A ⊗[R] A) (S : Set A)
-- given
  (hS : Algebra.adjoin R S = ⊤)
  (hgen : ∀ x ∈ S, (x ⊗ₜ[R] (1 : A)) * Δ = ((1 : A) ⊗ₜ[R] x) * Δ)
  (s : A) :
-- imply
  (s ⊗ₜ[R] (1 : A)) * Δ = ((1 : A) ⊗ₜ[R] s) * Δ := by
-- proof
  have hs : s ∈ Algebra.adjoin R S := by
    rw [hS]
    apply Algebra.mem_top
  induction hs using Algebra.adjoin_induction with
  | mem x hx => apply hgen x hx
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  | add x y _ _ hx hy =>
    rw [TensorProduct.add_tmul, TensorProduct.tmul_add, add_mul, add_mul, hx, hy]
  | mul x y _ _ hx hy =>
    have e1 : ((x * y) ⊗ₜ[R] (1 : A)) = (x ⊗ₜ[R] (1 : A)) * (y ⊗ₜ[R] (1 : A)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    have e2 : ((1 : A) ⊗ₜ[R] (x * y)) = ((1 : A) ⊗ₜ[R] x) * ((1 : A) ⊗ₜ[R] y) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rw [e1, e2, mul_assoc, hy, ← mul_assoc, mul_comm (x ⊗ₜ[R] (1 : A)), mul_assoc, hx, ← mul_assoc,
      mul_comm ((1 : A) ⊗ₜ[R] y) ((1 : A) ⊗ₜ[R] x)]


/--
[Algebra_tmul_one_mul_bezoutian_eq_one_tmul_mul](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_tmul_one_mul_bezoutian_eq_one_tmul_mul.lean)
-/
@[path]
private lemma main
  [CommRing R]
  {m : ℕ} {f : Fin m → MvPolynomial (Fin m) R}
  {a : Fin m → Fin m → MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin m) R}
-- given
  (ha : ∀ i, f i ⊗ₜ[R] (1 : MvPolynomial (Fin m) R) - (1 : MvPolynomial (Fin m) R) ⊗ₜ[R] f i =
    ∑ j, a i j * (MvPolynomial.X j ⊗ₜ[R] 1 - 1 ⊗ₜ[R] MvPolynomial.X j))
  {s : MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f)} :
-- imply
  (s ⊗ₜ[R] (1 : MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f))) *
      Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f)))
        (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f))) (Matrix.det (Matrix.of a)) =
    ((1 : MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f)) ⊗ₜ[R] s) *
      Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f)))
        (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f))) (Matrix.det (Matrix.of a)) := by
-- proof
  classical
  refine balanced_of_adjoin _
    (Set.range fun j : Fin m => (Ideal.Quotient.mk (Ideal.span (Set.range f)) (MvPolynomial.X j)))
    ?_ ?_ s
  ·
    rw [eq_top_iff]
    rintro y -
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hp : p ∈ Algebra.adjoin R (Set.range (MvPolynomial.X : Fin m → MvPolynomial (Fin m) R)) := by
      rw [MvPolynomial.adjoin_range_X]
      apply Algebra.mem_top
    have hrange : (Set.range fun j : Fin m =>
        (Ideal.Quotient.mk (Ideal.span (Set.range f)) (MvPolynomial.X j))) =
        (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f))) ''
          Set.range (MvPolynomial.X : Fin m → MvPolynomial (Fin m) R) := by
      ext y
      simp [Ideal.Quotient.mkₐ_eq_mk]
    rw [hrange, ← AlgHom.map_adjoin]
    exact ⟨p, hp, rfl⟩
  ·
    rintro _ ⟨j, rfl⟩
    have h := map_det_mul_map_eq_zero
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f)))
        (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f))))
      MvPolynomial.X f a ha (fun i => ?_) j
    ·
      rw [map_sub, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul] at h
      simp only [map_one, Ideal.Quotient.mkₐ_eq_mk] at h ⊢
      linear_combination h
    ·
      rw [map_sub, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
      simp only [map_one, Ideal.Quotient.mkₐ_eq_mk]
      have hfi : Ideal.Quotient.mk (Ideal.span (Set.range f)) (f i) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
      rw [hfi, TensorProduct.zero_tmul, TensorProduct.tmul_zero, sub_self]


-- created on 2026-10-13

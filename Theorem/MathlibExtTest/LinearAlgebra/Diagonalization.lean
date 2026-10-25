/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/Diagonalization.lean -/


import Lemma.Matrix.Diagonalization
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Trace


namespace MathlibExtTest.LinearAlgebra.Diagonalization

open MathlibExt.LinearAlgebra.DiagonalizationWanted

-- The eigenvalues in an eigenbasis of a semisimple split endomorphism sum to its trace.
example {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Fintype ι] [DecidableEq ι] (f : Module.End K V) (hs : f.IsSemisimple)
    (hsplit : f.charpoly.Splits) (hdim : Module.finrank K V = Fintype.card ι) :
    ∃ μ : ι → K, LinearMap.trace K V f = ∑ i, μ i := by
  obtain ⟨b, μ, heigen⟩ :=
    exists_eigenbasis_of_isSemisimple_of_splits f hs hsplit hdim
  refine ⟨μ, ?_⟩
  rw [LinearMap.trace_eq_matrix_trace K b]
  have hmatrix : LinearMap.toMatrix b b f = Matrix.diagonal μ := by
    ext i j
    rw [LinearMap.toMatrix_apply, (heigen j).apply_eq_smul, map_smul,
      Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one]
    by_cases hij : i = j
    · rw [hij, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
  rw [hmatrix, Matrix.trace_diagonal]

-- Every idempotent matrix over a field is similar to a diagonal matrix.
example {K n : Type*} [Field K] [Fintype n] [DecidableEq n] (A : Matrix n n K)
    (hA : A * A = A) :
    ∃ P D : Matrix n n K, D.IsDiag ∧ IsUnit P ∧ A = P * D * P⁻¹ := by
  let f : Module.End K (n → K) := Matrix.toLin' A
  have hf : IsIdempotentElem f := by
    change Matrix.toLin' A ∘ₗ Matrix.toLin' A = Matrix.toLin' A
    rw [← Matrix.toLin'_mul, hA]
  have hmin_dvd : minpoly K f ∣ Polynomial.X * (Polynomial.X - 1) := by
    apply minpoly.dvd K f
    simp only [map_mul, Polynomial.aeval_X, map_sub, map_one]
    rw [mul_sub, hf, mul_one, sub_self]
  have hsquare : Squarefree (Polynomial.X * (Polynomial.X - 1) : Polynomial K) := by
    have hcop : IsCoprime (Polynomial.X - Polynomial.C (0 : K))
        (Polynomial.X - Polynomial.C (1 : K)) :=
      Polynomial.pairwise_coprime_X_sub_C Function.injective_id zero_ne_one
    simpa using (squarefree_mul_iff.mpr
      ⟨hcop.isRelPrime, (Polynomial.irreducible_X_sub_C (0 : K)).squarefree,
        (Polynomial.irreducible_X_sub_C (1 : K)).squarefree⟩)
  have hsf : Squarefree (minpoly K f) := hsquare.squarefree_of_dvd hmin_dvd
  have hproj := LinearMap.IsIdempotentElem.isProj_range f hf
  have hsplit_f : f.charpoly.Splits := by
    rw [hproj.eq_conj_prodMap, LinearEquiv.charpoly_conj,
      LinearMap.charpoly_prodMap]
    change ((1 : Module.End K (LinearMap.range f)).charpoly *
      (0 : Module.End K (LinearMap.ker f)).charpoly).Splits
    rw [LinearMap.charpoly_one, LinearMap.charpoly_zero]
    exact ((Polynomial.Splits.X_sub_C 1).pow _).mul (Polynomial.Splits.X.pow _)
  apply exists_diagonal_similar_of_splits_of_squarefree_minpoly A
  · simpa [f, Matrix.charpoly_toLin'] using hsplit_f
  · simpa [f] using hsf

end MathlibExtTest.LinearAlgebra.Diagonalization

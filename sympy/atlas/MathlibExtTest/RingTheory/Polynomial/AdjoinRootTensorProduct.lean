/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/Polynomial/AdjoinRootTensorProduct.lean -/


import sympy.atlas.RingTheory.Polynomial.AdjoinRootTensorProduct
import Lemma.Ideal.Polynomial.AdjoinRootTensorProduct
import Mathlib.Algebra.Polynomial.RingDivision

set_option autoImplicit false

open scoped TensorProduct

/-- The algebraic CRT equivalence sends a quotient representative to the
same representative in every component. -/
noncomputable example (K R ι : Type*) [CommSemiring K] [CommRing R] [Algebra K R]
    [Finite ι] (I : ι → Ideal R)
    (h : Pairwise fun i j ↦ IsCoprime (I i) (I j)) (r : R) :
    Ideal.quotientInfAlgEquivPiQuotient K R ι I h (Ideal.Quotient.mk _ r) =
      fun i ↦ Ideal.Quotient.mk (I i) r := by
  rw [Ideal.quotientInfAlgEquivPiQuotient_mk]

/-- The product equivalence sends the distinguished root to the distinguished
root in every factor. -/
noncomputable example (K ι : Type*) [Field K] [Fintype ι]
    (g : ι → Polynomial K)
    (hcop : Pairwise fun i j ↦ IsCoprime (g i) (g j)) :
    AdjoinRoot.prodAlgEquiv g hcop (AdjoinRoot.root _) =
      fun i ↦ AdjoinRoot.root (g i) := by
  rw [AdjoinRoot.prodAlgEquiv_root]

/-- Generic check: `tensorProductAlgEquiv` has the stated `K'`-algebra type
under the local `rightAlgebra` instance. -/
noncomputable example (K K' : Type*) [Field K] [Field K'] [Algebra K K']
    (f : Polynomial K) :
    letI := Algebra.TensorProduct.rightAlgebra (R := K) (A := AdjoinRoot f)
      (B := K');
    (AdjoinRoot f ⊗[K] K') ≃ₐ[K'] AdjoinRoot (Polynomial.map (algebraMap K K') f) :=
  AdjoinRoot.tensorProductAlgEquiv f

/-- The base-change equivalence acts on a pure tensor by mapping its polynomial
representative and scaling by the right tensor factor. -/
noncomputable example (K K' : Type*) [Field K] [Field K'] [Algebra K K']
    (f p : Polynomial K) (c : K') :
    letI := Algebra.TensorProduct.rightAlgebra (R := K) (A := AdjoinRoot f)
      (B := K')
    AdjoinRoot.tensorProductAlgEquiv f (AdjoinRoot.mk f p ⊗ₜ[K] c) =
      AdjoinRoot.mk (Polynomial.map (algebraMap K K') f)
        (c • Polynomial.map (algebraMap K K') p) := by
  rw [AdjoinRoot.tensorProductAlgEquiv_mk_tmul]

/-- After decomposition, the distinguished root lands at the distinguished
root in each irreducible factor. -/
noncomputable example (K K' ι : Type*) [Field K] [Field K'] [Algebra K K']
    [Fintype ι] (f : Polynomial K) (g : ι → Polynomial K')
    (hirr : ∀ i, Irreducible (g i))
    (hne : Pairwise fun i j ↦ ¬Associated (g i) (g j))
    (hprod : Associated (Polynomial.map (algebraMap K K') f) (∏ i, g i))
    (i : ι) :
    letI := Algebra.TensorProduct.rightAlgebra (R := K) (A := AdjoinRoot f)
      (B := K')
    AdjoinRoot.tensorProductAlgEquivPi f g hirr hne hprod
        (AdjoinRoot.root f ⊗ₜ[K] (1 : K')) i = AdjoinRoot.root (g i) := by
  rw [AdjoinRoot.tensorProductAlgEquivPi_root_tmul_one_apply]

/-- One-factor specialization over `ℚ`: constant family at an arbitrary
irreducible `f`, with all three hypotheses proved in Lean. -/
noncomputable example (f : Polynomial ℚ) (hf : Irreducible f) :
    letI := Algebra.TensorProduct.rightAlgebra (R := ℚ) (A := AdjoinRoot f)
      (B := ℚ);
    Nonempty ((AdjoinRoot f ⊗[ℚ] ℚ) ≃ₐ[ℚ] ∀ _ : Fin 1, AdjoinRoot f) :=
  let g : Fin 1 → Polynomial ℚ := fun _ => f
  let hirr : ∀ i, Irreducible (g i) := fun _ => hf
  let hne : Pairwise fun i j => ¬Associated (g i) (g j) :=
    fun i j hij => absurd (Subsingleton.elim i j) hij
  let hprod : Associated (Polynomial.map (algebraMap ℚ ℚ) f) (∏ i, g i) := by
    have hmap : Polynomial.map (algebraMap ℚ ℚ) f = f := by simp
    have h1 : (∏ i, g i) = f := Fin.prod_univ_one g
    rw [hmap, h1]
  ⟨AdjoinRoot.tensorProductAlgEquivPi f g hirr hne hprod⟩

/-- Concrete two-factor CRT over `ℚ`: `X * (X - 1)` splits into two distinct
linear factors, exercising the public decomposition theorem. -/
noncomputable example :
    letI := Algebra.TensorProduct.rightAlgebra (R := ℚ)
      (A := AdjoinRoot (∏ i : Fin 2, (Polynomial.X - Polynomial.C (i : ℚ))))
      (B := ℚ);
    Nonempty ((AdjoinRoot (∏ i : Fin 2, (Polynomial.X - Polynomial.C (i : ℚ)))
      ⊗[ℚ] ℚ) ≃ₐ[ℚ]
      ∀ i : Fin 2, AdjoinRoot (Polynomial.X - Polynomial.C (i : ℚ))) := by
  classical
  let g : Fin 2 → Polynomial ℚ :=
    fun i => Polynomial.X - Polynomial.C (i : ℚ)
  have hirr : ∀ i, Irreducible (g i) :=
    fun i => Polynomial.irreducible_X_sub_C _
  have hcast : Function.Injective (fun i : Fin 2 => (i : ℚ)) := by
    intro a b hab
    have hmid : (a.val : ℚ) = (b.val : ℚ) := hab
    have hval : a.val = b.val := by exact_mod_cast hmid
    exact Fin.ext hval
  have hcop : Pairwise (Function.onFun IsCoprime g) :=
    Polynomial.pairwise_coprime_X_sub_C hcast
  have hne : Pairwise fun i j => ¬Associated (g i) (g j) := by
    intro i j hij hassoc
    have hcopij : IsCoprime (g i) (g j) := hcop hij
    have hunit : IsUnit (g j) := (hcopij.isUnit_of_associated hassoc).2
    have hirj : Irreducible (g j) := Polynomial.irreducible_X_sub_C _
    exact hirj.not_isUnit hunit
  have hprod :
      Associated (Polynomial.map (algebraMap ℚ ℚ) (∏ i, g i)) (∏ i, g i) := by
    have hmap : Polynomial.map (algebraMap ℚ ℚ) (∏ i, g i) = ∏ i, g i := by
      simp
    rw [hmap]
  exact ⟨AdjoinRoot.tensorProductAlgEquivPi (∏ i, g i) g hirr hne hprod⟩

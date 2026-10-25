import Lemma.DifferentFiltrationFormula.Main

set_option autoImplicit false

open IsLocalRing Polynomial

attribute [local instance] FractionRing.liftAlgebra

section DerivativeFactorisation

variable {A : Type*} [CommRing A]
variable {B : Type*} [CommRing B] [Algebra A B]
variable {G : Type*} [Group G] [MulSemiringAction G B]

theorem MulSemiringAction.aeval_smul_minpoly [SMulCommClass G A B] (σ : G) (x : B) :
    aeval (σ • x) (minpoly A x) = 0 := by
  have h : aeval (MulSemiringAction.toAlgHom A B σ x) (minpoly A x)
      = MulSemiringAction.toAlgHom A B σ (aeval x (minpoly A x)) :=
    Polynomial.aeval_algHom_apply _ x (minpoly A x)
  rwa [minpoly.aeval, map_zero, MulSemiringAction.toAlgHom_apply] at h

theorem aeval_derivative_minpoly_eq_prod_sub_smul [Fintype G] [DecidableEq G] (x : B)
    (hsplit : (minpoly A x).map (algebraMap A B) = ∏ σ : G, (X - C (σ • x))) :
    aeval x (derivative (minpoly A x)) = ∏ σ ∈ Finset.univ.erase (1 : G), (x - σ • x) := by
  rw [aeval_def, eval₂_eq_eval_map, ← derivative_map, hsplit,
    ← Finset.mul_prod_erase Finset.univ (fun σ : G => (X : B[X]) - C (σ • x))
      (Finset.mem_univ (1 : G)),
    one_smul, derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul,
    eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero, eval_prod]
  exact Finset.prod_congr rfl fun σ _ => by rw [eval_sub, eval_X, eval_C]

theorem span_aeval_derivative_minpoly_eq_prod_span_smul_sub [Fintype G] [DecidableEq G] (x : B)
    (hsplit : (minpoly A x).map (algebraMap A B) = ∏ σ : G, (X - C (σ • x))) :
    Ideal.span {aeval x (derivative (minpoly A x))}
      = ∏ σ ∈ Finset.univ.erase (1 : G), Ideal.span {σ • x - x} := by
  rw [aeval_derivative_minpoly_eq_prod_sub_smul x hsplit, ← Ideal.prod_span_singleton]
  refine Finset.prod_congr rfl fun σ _ => ?_
  rw [← neg_sub (σ • x) x, Ideal.span_singleton_neg]

end DerivativeFactorisation

section MonogenicDifferent

variable (A K L B : Type*)
variable [CommRing A] [Field K] [CommRing B] [Field L]
variable [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
variable [IsScalarTower A K L] [IsScalarTower A B L]
variable [IsDomain A] [IsFractionRing A K]
variable [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
variable [IsIntegrallyClosed A] [IsDedekindDomain B] [Module.IsTorsionFree A B]

theorem differentIdeal_eq_span_aeval_derivative_minpoly (x : B)
    (hxL : Algebra.adjoin K {algebraMap B L x} = ⊤)
    (hxB : Algebra.adjoin A {x} = ⊤) :
    differentIdeal A B = Ideal.span {aeval x (derivative (minpoly A x))} := by
  have h := conductor_mul_differentIdeal A K L x hxL
  rwa [conductor_eq_top_of_adjoin_eq_top hxB, ← Ideal.one_eq_top, one_mul] at h

variable (G : Type*) [Group G] [MulSemiringAction G B]

theorem differentIdeal_eq_prod_span_smul_sub [Fintype G] [DecidableEq G] (x : B)
    (hxL : Algebra.adjoin K {algebraMap B L x} = ⊤)
    (hxB : Algebra.adjoin A {x} = ⊤)
    (hsplit : (minpoly A x).map (algebraMap A B) = ∏ σ : G, (X - C (σ • x))) :
    differentIdeal A B = ∏ σ ∈ Finset.univ.erase (1 : G), Ideal.span {σ • x - x} := by
  rw [differentIdeal_eq_span_aeval_derivative_minpoly A K L B x hxL hxB,
    span_aeval_derivative_minpoly_eq_prod_span_smul_sub x hsplit]

theorem differentIdeal_eq_pow_sum_depthCount_of_monogenic
    [IsLocalRing B] [Fintype G] [DecidableEq G] (x : B)
    (hxL : Algebra.adjoin K {algebraMap B L x} = ⊤)
    (hxB : Algebra.adjoin A {x} = ⊤)
    (hsplit : (minpoly A x).map (algebraMap A B) = ∏ σ : G, (X - C (σ • x)))
    (N : ℕ)
    (hdepth : ∀ σ : G, σ ≠ 1 → Ideal.span {σ • x - x}
        = IsLocalRing.maximalIdeal B ^ lowerRamificationDepthCount B G N σ) :
    differentIdeal A B
      = IsLocalRing.maximalIdeal B
          ^ ∑ σ ∈ Finset.univ.erase (1 : G), lowerRamificationDepthCount B G N σ :=
  calc differentIdeal A B
      = ∏ σ ∈ Finset.univ.erase (1 : G), Ideal.span {σ • x - x} :=
        differentIdeal_eq_prod_span_smul_sub A K L B G x hxL hxB hsplit
    _ = ∏ σ ∈ Finset.univ.erase (1 : G),
          IsLocalRing.maximalIdeal B ^ lowerRamificationDepthCount B G N σ :=
        Finset.prod_congr rfl fun σ hσ => hdepth σ (Finset.ne_of_mem_erase hσ)
    _ = IsLocalRing.maximalIdeal B
          ^ ∑ σ ∈ Finset.univ.erase (1 : G), lowerRamificationDepthCount B G N σ :=
        Finset.prod_pow_eq_pow_sum _ _ _

theorem differentEqPowFiltrationSum_of_monogenic
    [IsLocalRing B] [Fintype G] [DecidableEq G] (x : B)
    (hxL : Algebra.adjoin K {algebraMap B L x} = ⊤)
    (hxB : Algebra.adjoin A {x} = ⊤)
    (hsplit : (minpoly A x).map (algebraMap A B) = ∏ σ : G, (X - C (σ • x)))
    {N : ℕ} (hN : IsLocalRing.lowerRamificationGroup B G N = ⊥)
    (hdepth : ∀ σ : G, σ ≠ 1 → Ideal.span {σ • x - x}
        = IsLocalRing.maximalIdeal B ^ lowerRamificationDepthCount B G N σ) :
    DifferentEqPowFiltrationSum A B G := by
  refine differentEqPowFiltrationSum_of_cutoff hN ?_
  rw [differentIdeal_eq_pow_sum_depthCount_of_monogenic A K L B G x hxL hxB hsplit N hdepth,
    sum_lowerRamificationDepthCount_erase_one]

end MonogenicDifferent

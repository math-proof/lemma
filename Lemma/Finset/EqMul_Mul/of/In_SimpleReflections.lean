import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.LieGroups.code.HeckeKL
open Polynomial


/--
[CoxeterGroupData.simple_cancel](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HeckeKL.lean)
-/
@[path]
lemma CoxeterGroupData.simple_cancel
  {C : CoxeterGroupData}
  {s : C.W}
  {w : C.W}
-- given
  (hs : s ∈ C.simpleReflections) :
-- imply
  s * (s * w) = w := by
-- proof
  rw [← mul_assoc, C.simple_sq s hs, one_mul]

private lemma CoxeterGroupData.length_zero_eq_one
  {C : CoxeterGroupData}
  {w : C.W}
-- given
  (h : C.length w = 0) :
-- imply
  w = 1 := by
-- proof
  by_contra hw; have := C.descentRefl_length w hw; omega

private lemma CoxeterGroupData.simple_ne_one
  {C : CoxeterGroupData}
  {s : C.W}
-- given
  (hs : s ∈ C.simpleReflections) :
-- imply
  s ≠ 1 := by
-- proof
  intro h; subst h; have := C.length_simple 1 hs; rw [C.length_one] at this; omega

private lemma CoxeterGroupData.descentRefl_of_simple
  {C : CoxeterGroupData}
  {s : C.W}
-- given
  (hs : s ∈ C.simpleReflections) :
-- imply
  C.descentRefl s = s := by
-- proof
  have hs_ne : s ≠ 1 := C.simple_ne_one s hs
  have h1 : C.length (C.descentRefl s * s) = 0 := by
    have := C.descentRefl_length s hs_ne
    have := C.length_simple s hs
    omega
  have h2 : C.descentRefl s * s = 1 := C.length_zero_eq_one _ h1
  calc C.descentRefl s = C.descentRefl s * 1 := (mul_one _).symm
    _ = C.descentRefl s * (s * s) := by rw [C.simple_sq s hs]
    _ = (C.descentRefl s * s) * s := (mul_assoc _ _ _).symm
    _ = 1 * s := by rw [h2]
    _ = s := one_mul s

private lemma simpleReflMulBasis_apply
  {C : CoxeterGroupData}
  {s y w : C.W} :
-- imply
  (simpleReflMulBasis C s y) w = if C.length (s * y) = C.length y + 1 then if s * y = w then 1 else 0 else (if y = w then hecke_q - 1 else 0) + (if s * y = w then hecke_q else 0) := by
-- proof
  simp only [simpleReflMulBasis, Finsupp.add_apply, Finsupp.single_apply]
  split_ifs <;> simp_all

private lemma heckeMul_single_single
  {C : CoxeterGroupData}
  {w₁ w₂ : C.W}
  {r₁ r₂ : HeckeCoeffRing} :
-- imply
  heckeMul C (Finsupp.single w₁ r₁) (Finsupp.single w₂ r₂) = (r₁ * r₂) • heckeMulBasis C w₁ w₂ := by
-- proof
  unfold heckeMul
  rw [Finsupp.sum_single_index (by simp [zero_mul, zero_smul, Finsupp.sum])]
  rw [Finsupp.sum_single_index (by simp [mul_zero, zero_smul])]

private lemma heckeMul_add_left
  {C : CoxeterGroupData}
  {f₁ f₂ g : HeckeAlgebra C} :
-- imply
  heckeMul C (f₁ + f₂) g = heckeMul C f₁ g + heckeMul C f₂ g := by
-- proof
  unfold heckeMul
  apply Finsupp.sum_add_index'
  · intro i; show g.sum (fun w₂ a₂ => (0 * a₂) • heckeMulBasis C i w₂) = 0
    simp [zero_mul, zero_smul, Finsupp.sum]
  · intro i b₁ b₂
    conv_lhs => arg 2; ext w₂ a₂; rw [add_mul, add_smul]
    rw [← Finsupp.sum_add]

private lemma heckeMul_add_right
  {C : CoxeterGroupData}
  {f g₁ g₂ : HeckeAlgebra C} :
-- imply
  heckeMul C f (g₁ + g₂) = heckeMul C f g₁ + heckeMul C f g₂ := by
-- proof
  unfold heckeMul
  have inner_split : ∀ w₁ a₁,
    (g₁ + g₂).sum (fun w₂ a₂ => (a₁ * a₂) • heckeMulBasis C w₁ w₂) =
    g₁.sum (fun w₂ a₂ => (a₁ * a₂) • heckeMulBasis C w₁ w₂) +
    g₂.sum (fun w₂ a₂ => (a₁ * a₂) • heckeMulBasis C w₁ w₂) := by
    intro w₁ a₁
    apply Finsupp.sum_add_index'
    · intro i; simp
    · intro i b₁ b₂; rw [mul_add, add_smul]
  conv_lhs => arg 2; ext w₁ a₁; rw [inner_split w₁ a₁]
  rw [← Finsupp.sum_add]

private lemma heckeStdBasis_eq_T
  {C : CoxeterGroupData}
  {w : C.W} :
-- imply
  heckeStdBasis C w = HeckeAlgebra.T C w := by
-- proof
  show Finsupp.basisSingleOne w = Finsupp.single w 1
  simp [Finsupp.basisSingleOne]

private lemma heckeStdBasis_coe_eq_T
  {C : CoxeterGroupData} :
-- imply
  (heckeStdBasis C : C.W → HeckeAlgebra C) = HeckeAlgebra.T C :=
-- proof
  funext (heckeStdBasis_eq_T C)

private lemma hecke_basis
  {C : CoxeterGroupData} :
-- imply
  LinearIndependent HeckeCoeffRing (HeckeAlgebra.T C) ∧ Submodule.span HeckeCoeffRing (Set.range (HeckeAlgebra.T C)) = ⊤ := by
-- proof
  have hcoe := heckeStdBasis_coe_eq_T C
  exact ⟨hcoe ▸ (heckeStdBasis C).linearIndependent, hcoe ▸ (heckeStdBasis C).span_eq⟩

private lemma hecke_basis_injective
  {C : CoxeterGroupData} :
-- imply
  Function.Injective (HeckeAlgebra.T C) :=
-- proof
  (hecke_basis C).1.injective

private lemma coeffInvolution_involutive
-- imply
  Function.Involutive coeffInvolution := by
-- proof
  intro x
  simp only [coeffInvolution]
  rw [← Finsupp.mapDomain_comp]
  simp [Finsupp.mapDomain_id]

private lemma coeffInvolution_T
  {n : ℤ} :
-- imply
  coeffInvolution (LaurentPolynomial.T n) = LaurentPolynomial.T (-n) := by
-- proof
  unfold coeffInvolution LaurentPolynomial.T
  rw [Finsupp.mapDomain_single]

private lemma coeffInvolution_mul
  {a b : HeckeCoeffRing} :
-- imply
  coeffInvolution (a * b) = coeffInvolution a * coeffInvolution b := by
-- proof
  rw [coeffInvolution_eq_ringHom, coeffInvolution_eq_ringHom, coeffInvolution_eq_ringHom]
  exact map_mul coeffInvolutionRingHom a b

private lemma HeckeAlgebra.D_single
  {C : CoxeterGroupData}
  {w : C.W}
  {c : HeckeCoeffRing} :
-- imply
  HeckeAlgebra.D C (Finsupp.single w c) = coeffInvolution c • D_on_basis C w := by
-- proof
  unfold HeckeAlgebra.D
  rw [Finsupp.sum_single_index]
  simp [coeffInvolution_zero]
attribute [-instance] HeckeAlgebra.instRing HeckeAlgebra.instAlgebra in

private lemma HeckeAlgebra.D_semilinear
  {C : CoxeterGroupData}
  {a : HeckeCoeffRing}
-- given
  (h : HeckeAlgebra C) :
-- imply
  HeckeAlgebra.D C (a • h) = coeffInvolution a • HeckeAlgebra.D C h := by
-- proof
  unfold HeckeAlgebra.D
  calc Finsupp.sum (a • h) (fun w aw => coeffInvolution aw • D_on_basis C w)
    = Finsupp.sum h (fun i c => coeffInvolution (a • c) • D_on_basis C i) := by
      exact Finsupp.sum_smul_index' (fun i => by simp [coeffInvolution_zero])
    _ = Finsupp.sum h (fun i c => coeffInvolution a • (coeffInvolution c • D_on_basis C i)) := by
      congr 1; ext i c; rw [show a • c = a * c from rfl, coeffInvolution_mul, mul_smul]
    _ = coeffInvolution a • Finsupp.sum h (fun w aw => coeffInvolution aw • D_on_basis C w) := by
      rw [← Finsupp.smul_sum]
attribute [-instance] HeckeAlgebra.instRing HeckeAlgebra.instAlgebra in

private lemma HeckeAlgebra.D_finset_sum
  {C : CoxeterGroupData}
  {s : Finset ι}
  {f : ι → HeckeAlgebra C} :
-- imply
  HeckeAlgebra.D C (∑ i ∈ s, f i) = ∑ i ∈ s, HeckeAlgebra.D C (f i) :=
-- proof
  map_sum (HeckeAlgebra.D_addHom C) f s

private lemma finset_sum_single
  [DecidableEq α]
  [AddCommMonoid β]
  {s : Finset ι}
  {y : α}
  {f : ι → β} :
-- imply
  ∑ i ∈ s, Finsupp.single y (f i) = Finsupp.single y (∑ i ∈ s, f i) :=
-- proof
  (map_sum (Finsupp.singleAddHom y) f s).symm
attribute [-instance] HeckeAlgebra.instRing HeckeAlgebra.instAlgebra in

private lemma smul_D_on_basis
  {C : CoxeterGroupData}
  {c : HeckeCoeffRing}
  {x : C.W} :
-- imply
  c • D_on_basis C x = ∑ y : C.W, Finsupp.single y (c * D_coeff C y x) := by
-- proof
  show c • (∑ z : C.W, Finsupp.single z (D_coeff C z x)) = _
  rw [Finset.smul_sum]
  congr 1; ext y
  rw [Finsupp.smul_single, smul_eq_mul]

private lemma RPoly_unfold_lt
  {C : CoxeterGroupData}
  {x y : C.W}
-- given
  (hy : y ≠ 1)
  (hlt : C.length (C.descentRefl y * x) < C.length x) :
-- imply
  RPoly C x y = RPoly C (C.descentRefl y * x) (C.descentRefl y * y) := by
-- proof
  conv_lhs => rw [RPoly]
  simp only [dif_neg hy]
  simp only [hlt, ite_true]

private lemma RPoly_unfold_ge
  {C : CoxeterGroupData}
  {x y : C.W}
-- given
  (hy : y ≠ 1)
  (hge : ¬ C.length (C.descentRefl y * x) < C.length x) :
-- imply
  RPoly C x y = (Polynomial.X - Polynomial.C 1) * RPoly C x (C.descentRefl y * y) + Polynomial.X * RPoly C (C.descentRefl y * x) (C.descentRefl y * y) := by
-- proof
  conv_lhs => rw [RPoly]
  simp only [dif_neg hy]
  simp only [hge, ite_false]

private lemma sum_single_ite_eq
  {C : CoxeterGroupData}
  {w : C.W} :
-- imply
  ∑ y : C.W, Finsupp.single y (if y = w then (1 : HeckeCoeffRing) else 0) = Finsupp.single w 1 := by
-- proof
  have : ∀ y : C.W, Finsupp.single y (if y = w then (1 : HeckeCoeffRing) else 0) =
    if y = w then Finsupp.single y 1 else 0 := by
    intro y
    split_ifs with h
    · rfl
    · exact (Finsupp.single_zero (a := y) : Finsupp.single y (0 : HeckeCoeffRing) = 0)
  simp_rw [this]
  rw [Finset.sum_ite_eq']
  simp [Finset.mem_univ]
attribute [-instance] HeckeAlgebra.instRing HeckeAlgebra.instAlgebra in

private lemma mkBoundedPoly_natDegree_le
  {bound : ℕ}
  {coeffs : ℕ → ℤ} :
-- imply
  (mkBoundedPoly bound coeffs).natDegree ≤ bound := by
-- proof
  unfold mkBoundedPoly
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  calc (Polynomial.C (coeffs i) * Polynomial.X ^ i).natDegree
    ≤ i := Polynomial.natDegree_C_mul_X_pow_le (coeffs i) i
    _ ≤ bound := by rw [Finset.mem_range] at hi; omega

private lemma poly_eq_mkBoundedPoly_of_deg_le
  {p : Polynomial ℤ}
  {bound : ℕ}
-- given
  (hdeg : p.natDegree ≤ bound) :
-- imply
  p = mkBoundedPoly bound (fun j => p.coeff j) := by
-- proof
  unfold mkBoundedPoly
  conv_lhs => rw [p.as_sum_range' (bound + 1) (by omega)]
  congr 1; ext i
  simp only [Polynomial.coeff_monomial, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    mul_ite, mul_one, mul_zero]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · rfl

private lemma mkBoundedPoly_congr
  {bound : ℕ}
  {f g : ℕ → ℤ}
-- given
  (h : ∀ j, j ≤ bound → f j = g j) :
-- imply
  mkBoundedPoly bound f = mkBoundedPoly bound g := by
-- proof
  simp only [mkBoundedPoly]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  rw [h i (by omega)]

private lemma kl_poly_zero_unless_bruhat_le
  {C : CoxeterGroupData}
  {y w : C.W} :
-- imply
  ¬ C.bruhatLE y w → KazhdanLusztigPoly C y w = 0 := by
-- proof
  intro h
  unfold KazhdanLusztigPoly
  simp [h]

private lemma kl_poly_diag
  {C : CoxeterGroupData}
  {w : C.W} :
-- imply
  KazhdanLusztigPoly C w w = 1 := by
-- proof
  unfold KazhdanLusztigPoly
  simp [C.bruhat_refl w]

private lemma klp_unfold
  {C : CoxeterGroupData}
  {y w : C.W}
-- given
  (hle : C.bruhatLE y w)
  (hne : y ≠ w) :
-- imply
  KazhdanLusztigPoly C y w = mkBoundedPoly ((C.length w - C.length y - 1) / 2) (self_dual_coeffs C y w ((C.length w - C.length y - 1) / 2) (fun z => if C.bruhatLE y z ∧ z ≠ y ∧ C.bruhatLE z w then KazhdanLusztigPoly C z w else 0)) := by
-- proof
  conv_lhs => rw [KazhdanLusztigPoly]
  simp only [hle, hne, ite_false, not_true_eq_false, dite_eq_ite]

private lemma kl_poly_unique
  {C : CoxeterGroupData}
  {Q : C.W → C.W → Polynomial ℤ}
  {y w : C.W}
-- given
  (hQ_zero : ∀ y w, ¬ C.bruhatLE y w → Q y w = 0)
  (hQ_diag : ∀ w, Q w w = 1)
  (hQ_deg : ∀ y w, C.bruhatLE y w → y ≠ w → (Q y w).natDegree ≤ (C.length w - C.length y - 1) / 2)
  (hQ_recursion : ∀ y w, C.bruhatLE y w → y ≠ w → Q y w = mkBoundedPoly ((C.length w - C.length y - 1) / 2) (self_dual_coeffs C y w ((C.length w - C.length y - 1) / 2) (fun z => if C.bruhatLE y z ∧ z ≠ y ∧ C.bruhatLE z w then Q z w else 0))) :
-- imply
  Q y w = KazhdanLusztigPoly C y w := by
-- proof
  suffices key : ∀ (n : ℕ) (y' w' : C.W),
    C.length w' - C.length y' = n →
    Q y' w' = KazhdanLusztigPoly C y' w' from
    key (C.length w - C.length y) y w rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro y' w' hdiff
    by_cases hle : C.bruhatLE y' w'
    ·
      by_cases heq : y' = w'
      ·
        subst heq
        rw [hQ_diag, kl_poly_diag]
      ·
        have hlen_lt : C.length y' < C.length w' :=
          C.bruhat_length_strict y' w' hle heq
        have ih_applied : ∀ z : C.W, C.length y' < C.length z →
          C.bruhatLE z w' → Q z w' = KazhdanLusztigPoly C z w' := by
          intro z hz_gt hz_le
          apply ih (C.length w' - C.length z)
          · omega
          · rfl
        have hQ_rec := hQ_recursion y' w' hle heq
        have rec_eq : (fun z => if C.bruhatLE y' z ∧ z ≠ y' ∧ C.bruhatLE z w'
          then Q z w' else 0) =
          (fun z => if C.bruhatLE y' z ∧ z ≠ y' ∧ C.bruhatLE z w'
          then KazhdanLusztigPoly C z w' else 0) := by
          funext z
          split_ifs with h
          · exact ih_applied z
            (C.bruhat_length_strict y' z h.1 (Ne.symm h.2.1)) h.2.2
          · rfl
        rw [rec_eq] at hQ_rec
        rw [hQ_rec, klp_unfold C y' w' hle heq]
    ·
      rw [hQ_zero y' w' hle, kl_poly_zero_unless_bruhat_le C y' w' hle]

private lemma simpleActOnLinComb_single_eq
  {C : CoxeterGroupData}
  {s w : C.W}
  {c : HeckeCoeffRing} :
-- imply
  simpleActOnLinComb C s (Finsupp.single w c) = c • simpleReflMulBasis C s w := by
-- proof
  apply simpleActOnLinComb_single C s w c

private lemma heckeMulBasis_one_left_eq
  {C : CoxeterGroupData}
  {w : C.W} :
-- imply
  heckeMulBasis C 1 w = Finsupp.single w 1 := by
-- proof
  apply heckeMulBasis_one_left C w

private lemma heckeMulBasis_one_right_eq
  {C : CoxeterGroupData}
  {w₁ : C.W} :
-- imply
  heckeMulBasis C w₁ 1 = Finsupp.single w₁ 1 := by
-- proof
  apply heckeMulBasis_one_right C w₁

private lemma heckeMulBasis_simple_eq
  {C : CoxeterGroupData}
  {s : C.W}
  {w : C.W}
-- given
  (hs : s ∈ C.simpleReflections) :
-- imply
  heckeMulBasis C s w = simpleReflMulBasis C s w := by
-- proof
  apply heckeMulBasis_simple C s hs w

private lemma heckeMulBasis_descent_eq
  {C : CoxeterGroupData}
  {w₁ : C.W}
-- given
  (hw₁ : w₁ ≠ 1) :
-- imply
  heckeMulBasis C (C.descentRefl w₁) (C.descentRefl w₁ * w₁) = Finsupp.single w₁ 1 := by
-- proof
  apply heckeMulBasis_descent C w₁ hw₁

private lemma heckeMulBasis_unfold_eq
  {C : CoxeterGroupData}
  {w₁ : C.W}
  {w₂ : C.W}
-- given
  (hw₁ : w₁ ≠ 1) :
-- imply
  heckeMulBasis C w₁ w₂ = simpleActOnLinComb C (C.descentRefl w₁) (heckeMulBasis C (C.descentRefl w₁ * w₁) w₂) := by
-- proof
  apply heckeMulBasis_unfold C w₁ hw₁ w₂

private lemma simpleActOnLinComb_add_eq
  {C : CoxeterGroupData}
  {s : C.W}
  {f g : HeckeAlgebra C} :
-- imply
  simpleActOnLinComb C s (f + g) = simpleActOnLinComb C s f + simpleActOnLinComb C s g := by
-- proof
  apply simpleActOnLinComb_add C s f g

private lemma simpleActOnLinComb_quadratic_eq
  {C : CoxeterGroupData}
  {s : C.W}
  {w : C.W}
-- given
  (hs : s ∈ C.simpleReflections) :
-- imply
  simpleActOnLinComb C s (simpleReflMulBasis C s w) = hecke_q • Finsupp.single w 1 + (hecke_q - 1) • simpleReflMulBasis C s w := by
-- proof
  apply simpleActOnLinComb_quadratic C s hs w

private lemma simpleActOnLinComb_smul_eq
  {C : CoxeterGroupData}
  {s : C.W}
  {c : HeckeCoeffRing}
  {f : HeckeAlgebra C} :
-- imply
  simpleActOnLinComb C s (c • f) = c • simpleActOnLinComb C s f := by
-- proof
  apply simpleActOnLinComb_smul C s c f

private lemma heckeMulBasis_assoc_gen_rhs_eq
  {C : CoxeterGroupData}
  {s : C.W}
  {w₂ w₃ : C.W}
-- given
  (hs : s ∈ C.simpleReflections) :
-- imply
  (heckeMulBasis C w₂ w₃).sum (fun v c => c • heckeMulBasis C s v) = simpleActOnLinComb C s (heckeMulBasis C w₂ w₃) := by
-- proof
  apply heckeMulBasis_assoc_gen_rhs C s hs w₂ w₃

private lemma simpleActOnLinComb_quadratic_gen_eq
  {C : CoxeterGroupData}
  {s : C.W}
  {f : HeckeAlgebra C}
-- given
  (hs : s ∈ C.simpleReflections) :
-- imply
  simpleActOnLinComb C s (simpleActOnLinComb C s f) = (hecke_q - 1) • simpleActOnLinComb C s f + hecke_q • f := by
-- proof
  apply simpleActOnLinComb_quadratic_gen C s hs f

private lemma heckeMulBasis_assoc_gen_eq
  {C : CoxeterGroupData}
  {s : C.W}
  {w₂ w₃ : C.W}
-- given
  (hs : s ∈ C.simpleReflections) :
-- imply
  (heckeMulBasis C s w₂).sum (fun v c => c • heckeMulBasis C v w₃) = (heckeMulBasis C w₂ w₃).sum (fun v c => c • heckeMulBasis C s v) := by
-- proof
  apply heckeMulBasis_assoc_gen C s hs w₂ w₃

private lemma finsupp_sum_comm_smul_eq
  [CommRing R]
  {g : W → W →₀ R}
  {outer : W →₀ R}
  {inner : W → W →₀ R} :
-- imply
  outer.sum (fun v c => c • (inner v).sum (fun u d => d • g u)) = (outer.sum (fun v c => c • inner v)).sum (fun u d => d • g u) := by
-- proof
  apply finsupp_sum_comm_smul g outer inner

private lemma heckeMulBasis_assoc_eq
  {C : CoxeterGroupData}
  {w₁ w₂ w₃ : C.W} :
-- imply
  (heckeMulBasis C w₁ w₂).sum (fun v c => c • heckeMulBasis C v w₃) = (heckeMulBasis C w₂ w₃).sum (fun v c => c • heckeMulBasis C w₁ v) := by
-- proof
  apply heckeMulBasis_assoc C w₁ w₂ w₃

private lemma coeffInvolution_eq_ringHom_eq
  {a : HeckeCoeffRing} :
-- imply
  coeffInvolution a = coeffInvolutionRingHom a := by
-- proof
  apply coeffInvolution_eq_ringHom a

private lemma coeffInvolution_zero_eq :
-- imply
  coeffInvolution 0 = 0 := by
-- proof
  apply coeffInvolution_zero

private lemma coeffInvolution_add_eq
  {a b : HeckeCoeffRing} :
-- imply
  coeffInvolution (a + b) = coeffInvolution a + coeffInvolution b := by
-- proof
  apply coeffInvolution_add a b

private lemma D_zero_eq
  {C : CoxeterGroupData} :
-- imply
  HeckeAlgebra.D C 0 = 0 := by
-- proof
  apply HeckeAlgebra.D_zero C

private lemma D_add_eq
  {C : CoxeterGroupData}
  {f g : HeckeAlgebra C} :
-- imply
  HeckeAlgebra.D C (f + g) = HeckeAlgebra.D C f + HeckeAlgebra.D C g := by
-- proof
  apply HeckeAlgebra.D_add C f g


-- created on 2026-10-24

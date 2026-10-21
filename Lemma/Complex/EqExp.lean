import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[IntermediateField_exists_ringHom_complex_apply_eq_exp_of_isPrimitiveRoot](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IntermediateField_exists_ringHom_complex_apply_eq_exp_of_isPrimitiveRoot.lean)
-/
@[path]
private lemma main
  (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
  (q : ℕ) [NeZero q]
  (ξ : ↥k₀) (hξ : IsPrimitiveRoot ξ q) :
  -- imply
  ∃ ι : RingHom ↥k₀ ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / q) := by
  -- proof
  classical
  have hq0 : q ≠ 0 := NeZero.ne q
  have hq : 0 < q := Nat.pos_of_ne_zero hq0
  obtain ⟨ζ, hζdef⟩ : ∃ z : ℂ, z = Complex.exp (2 * Real.pi * Complex.I / q) := ⟨_, rfl⟩
  have hζ : IsPrimitiveRoot ζ q := by
    rw [hζdef]
    apply Complex.isPrimitiveRoot_exp q hq0
  let _ : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  let _ : Algebra.IsAlgebraic ℚ ↥k₀ := Algebra.IsAlgebraic.of_injective k₀.val (RingHom.injective _)
  have hint : IsIntegral ℚ ξ := Algebra.IsIntegral.isIntegral ξ
  have hmin : minpoly ℚ ξ = Polynomial.cyclotomic q ℚ := (Polynomial.cyclotomic_eq_minpoly_rat hξ hq).symm
  have hζroot : ζ ∈ (minpoly ℚ ξ).aroots ℂ := by
    rw [Polynomial.mem_aroots, hmin]
    refine ⟨Polynomial.cyclotomic_ne_zero q ℚ, ?_⟩
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, Polynomial.map_cyclotomic, ← Polynomial.IsRoot.def, Polynomial.isRoot_cyclotomic_iff]
    apply hζ
  let φ₀ : AlgHom ℚ ↥(IntermediateField.adjoin ℚ ({ξ} : Set ↥k₀)) ℂ := (IntermediateField.algHomAdjoinIntegralEquiv ℚ hint).symm ⟨ζ, hζroot⟩
  have hφ₀ : φ₀ (IntermediateField.AdjoinSimple.gen ℚ ξ) = ζ := IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen ℚ hint ⟨ζ, hζroot⟩
  let algF : Algebra ↥(IntermediateField.adjoin ℚ ({ξ} : Set ↥k₀)) ℂ := φ₀.toRingHom.toAlgebra
  let _ : Algebra.IsAlgebraic ↥(IntermediateField.adjoin ℚ ({ξ} : Set ↥k₀)) ↥k₀ := Algebra.IsAlgebraic.tower_top (K := ℚ) ↥(IntermediateField.adjoin ℚ ({ξ} : Set ↥k₀))
  let ι : AlgHom ↥(IntermediateField.adjoin ℚ ({ξ} : Set ↥k₀)) ↥k₀ ℂ := IsAlgClosed.lift
  refine ⟨ι.toRingHom, ?_⟩
  rw [← hζdef]
  have h2 : ι ξ = algebraMap ↥(IntermediateField.adjoin ℚ ({ξ} : Set ↥k₀)) ℂ (IntermediateField.AdjoinSimple.gen ℚ ξ) := ι.commutes (IntermediateField.AdjoinSimple.gen ℚ ξ)
  refine h2.trans hφ₀


-- created on 2026-10-20

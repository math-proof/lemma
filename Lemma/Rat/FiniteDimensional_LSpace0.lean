import Mathlib
import sympy.Basic
import Lemma.AlgebraicCurve.AdelicIndex
import Lemma.Scheme.IsCurveOver
import Lemma.Int.P2MUtil

open AlgebraicCurve

/--
[AlgebraicCurve_finiteDimensional_lSpace_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_finiteDimensional_lSpace_zero.lean)
-/
@[path]
private lemma main
  {K : Type u} [Field K]
  {F : Type v} [Field F] [Algebra K F] [IsCurveOver K F] [Algebra.EssFiniteType K F] [Nonempty (Place K F)] :
-- imply
  FiniteDimensional K (LSpace (0 : Divisor K F)) := by
  classical
    have hord : ∀ f : F, f ∈ LSpace (0 : Divisor K F) → f ≠ 0 →
        ∀ v : Place K F, v.ord f = 0 := by
-- proof
      intro f hf hf0
      have hnn : ∀ v : Place K F, 0 ≤ v.ord f := by
        rcases (mem_lSpace_iff_ord).mp hf with h0 | h
        · exact absurd h0 hf0
        ·
          intro v
          simpa using h v
      obtain ⟨D, hDord, hDdeg⟩ :=
        HasPrincipalDivisors.exists_divisor (K := K) (F := F) f hf0
      have hdeg_sum : Divisor.degree D = D.sum (fun w n => n * (w.deg : ℤ)) := by
        simp [Divisor.degree, Finsupp.liftAddHom_apply, AddMonoidHom.coe_mulRight]
      have hdegpos : ∀ w : Place K F, 0 < (w.deg : ℤ) := by
        intro w
        have : Module.Finite K w.ResidueField := IsCurveOver.finiteResidue w
        exact_mod_cast Module.finrank_pos
      have hterm : ∀ w ∈ D.support, D w * (w.deg : ℤ) = 0 := by
        refine (Finset.sum_eq_zero_iff_of_nonneg ?_).mp ?_
        ·
          intro w _
          exact mul_nonneg (hDord w ▸ hnn w) (le_of_lt (hdegpos w))
        ·
          have h := hDdeg
          rwa [hdeg_sum] at h
      have hD0 : ∀ w : Place K F, D w = 0 := by
        intro w
        by_cases hw : w ∈ D.support
        ·
          rcases mul_eq_zero.mp (hterm w hw) with h | h
          · exact h
          · exact absurd h (ne_of_gt (hdegpos w))
        · exact Finsupp.notMem_support_iff.mp hw
      intro v
      rw [← hDord v]; exact hD0 v
    obtain ⟨v₀⟩ := ‹Nonempty (Place K F)›
    have hmem : ∀ f : LSpace (0 : Divisor K F), (f : F) ∈ v₀.toValuationSubring := by
      intro f
      by_cases hf0 : (f : F) = 0
      ·
        rw [hf0]
        exact zero_mem _
      ·
        obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v₀.toValuationSubring
        obtain ⟨u, hu⟩ := v₀.exists_unit_mul_zpow hf0 hπ
        rw [hord f f.2 hf0 v₀, zpow_zero, mul_one] at hu
        rw [hu]; exact (u : v₀.toValuationSubring).2
    let φ : LSpace (0 : Divisor K F) →ₗ[K] v₀.ResidueField :=
      { toFun := fun f => IsLocalRing.residue _ (⟨f, hmem f⟩ : v₀.toValuationSubring)
        map_add' := by
          intro f g
          have h : (⟨((f + g : LSpace (0 : Divisor K F)) : F), hmem (f + g)⟩ :
              v₀.toValuationSubring) = ⟨f, hmem f⟩ + ⟨g, hmem g⟩ := rfl
          rw [h, map_add]
        map_smul' := by
          intro k f
          have h : (⟨((k • f : LSpace (0 : Divisor K F)) : F), hmem (k • f)⟩ :
              v₀.toValuationSubring) = algebraMap K v₀.toValuationSubring k * ⟨f, hmem f⟩ := by
            apply Subtype.ext
            show (k • (f : F)) = _
            rw [Algebra.smul_def]; rfl
          rw [h, map_mul]
          show algebraMap K v₀.ResidueField k * _ = k • _
          rw [Algebra.smul_def] }
    have hker : ∀ f : LSpace (0 : Divisor K F), φ f = 0 → f = 0 := by
      intro f hφf
      by_contra hf
      have hf0 : (f : F) ≠ 0 := fun h => hf (Subtype.ext h)
      obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v₀.toValuationSubring
      obtain ⟨u, hu⟩ := v₀.exists_unit_mul_zpow hf0 hπ
      rw [hord f f.2 hf0 v₀, zpow_zero, mul_one] at hu
      have huf : (⟨f, hmem f⟩ : v₀.toValuationSubring) = (u : v₀.toValuationSubring) :=
        Subtype.ext hu
      have : IsUnit (φ f) := by
        show IsUnit (IsLocalRing.residue _ (⟨f, hmem f⟩ : v₀.toValuationSubring))
        rw [huf]
        exact (IsLocalRing.residue _).isUnit_map u.isUnit
      rw [hφf] at this
      exact this.ne_zero rfl
    have : Module.Finite K v₀.ResidueField := IsCurveOver.finiteResidue v₀
    exact FiniteDimensional.of_injective φ ((injective_iff_map_eq_zero φ).mpr hker)


-- created on 2026-10-23

import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Def.Analysis.SpecialFunctions.Elliptic.FundamentalParallelogram.Part2
/-!
# Fundamental parallelograms of complex lattices
-/


namespace PeriodPair

/-- At the origin, the fundamental parallelogram is the standard fundamental domain. -/
@[simp]
theorem fundamentalParallelogram_zero (L : PeriodPair) :
    L.fundamentalParallelogram 0 = ZSpan.fundamentalDomain L.basis := by
  simp [fundamentalParallelogram]

/-- The coordinates of a linear combination of the two periods. -/
theorem basis_repr_omega (L : PeriodPair) (t₁ t₂ : ℝ) (i : Fin 2) :
    L.basis.repr (t₁ • L.ω₁ + t₂ • L.ω₂) i = ![t₁, t₂] i := by
  rw [show t₁ • L.ω₁ + t₂ • L.ω₂ = t₁ • L.basis 0 + t₂ • L.basis 1 from by simp]
  simp only [map_add, map_smul, Module.Basis.repr_self, Finsupp.smul_single,
    smul_eq_mul, mul_one, Finsupp.add_apply, Finsupp.single_apply]
  fin_cases i <;>
    simp [show (1 : Fin 2) ≠ 0 from by decide, show (0 : Fin 2) ≠ 1 from by decide]

/-- Membership in a fundamental parallelogram in terms of the two period coordinates. -/
theorem mem_fundamentalParallelogram_iff (L : PeriodPair) {α z : ℂ} :
    z ∈ L.fundamentalParallelogram α ↔
      ∃ t₁ t₂ : ℝ, 0 ≤ t₁ ∧ t₁ < 1 ∧ 0 ≤ t₂ ∧ t₂ < 1 ∧
        z = α + t₁ • L.ω₁ + t₂ • L.ω₂ := by
  simp only [fundamentalParallelogram, Set.mem_image, ZSpan.mem_fundamentalDomain]
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨L.basis.repr w 0, L.basis.repr w 1, (hw 0).1, (hw 0).2,
      (hw 1).1, (hw 1).2, ?_⟩
    have hw_repr : w = L.basis.repr w 0 • L.ω₁ + L.basis.repr w 1 • L.ω₂ := by
      have h := L.basis.sum_repr w
      rw [Fin.sum_univ_two, L.basis_zero, L.basis_one] at h
      exact h.symm
    calc
      α + w = α + (L.basis.repr w 0 • L.ω₁ + L.basis.repr w 1 • L.ω₂) :=
        congrArg (α + ·) hw_repr
      _ = α + L.basis.repr w 0 • L.ω₁ + L.basis.repr w 1 • L.ω₂ := by abel
  · rintro ⟨t₁, t₂, h1, h2, h3, h4, rfl⟩
    refine ⟨t₁ • L.ω₁ + t₂ • L.ω₂, fun i ↦ ?_, by abel⟩
    rw [L.basis_repr_omega]
    fin_cases i
    · simpa using ⟨h1, h2⟩
    · simpa using ⟨h3, h4⟩

end PeriodPair

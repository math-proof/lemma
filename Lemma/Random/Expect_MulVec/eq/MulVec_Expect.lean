import Mathlib.Data.Matrix.Mul
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.WithDensity
import sympy.stats.joint_rv
import sympy.Basic


/--
Pull a constant Mathlib matrix–vector product (`*ᵥ` / `Matrix.mulVec`) through
(unconditional) expectation, componentwise.

Renamed out of `Expect_Dot` (which is reserved for Tensor `@` / `Dot.dot`).

| attributes | lemma |
| :---: | :---: |
| main | Random.Expect_MulVec.eq.MulVec_Expect |
| comm | Random.MulVec_Expect.eq.Expect_MulVec |
-/
@[main, comm]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α]
  [Countable α] [MeasurableSingletonClass α]
  {π : MeasureTheory.Measure Ω} {m n : ℕ}
  {a : Ω → α}
  {f : α → Fin n → ENNReal}
-- given
  (hP : PSpace π a)
  (A : Matrix (Fin m) (Fin n) ENNReal)
  (hf : ∀ i : Fin n, Measurable (fun x : α ↦ f x i)) :
-- imply
  (fun j : Fin m ↦ 𝔼[a: π](Matrix.mulVec A (f a) j)) =
    Matrix.mulVec A (fun i : Fin n ↦ 𝔼[a: π](f a i)) := by
-- proof
  ext j
  simp only [Expectation.ofRV, expectation_ennreal, Matrix.mulVec, dotProduct]
  -- ∫⁻ ∑ᵢ Aⱼᵢ fᵢ = ∑ᵢ ∫⁻ Aⱼᵢ fᵢ = ∑ᵢ Aⱼᵢ ∫⁻ fᵢ
  rw [MeasureTheory.lintegral_finsetSum (μ := π.map a) (Finset.univ : Finset (Fin n))
    fun i _ => (hf i).const_mul (A j i)]
  refine Finset.sum_congr rfl ?_
  intro i _
  exact MeasureTheory.lintegral_const_mul (A j i) (hf i)


-- created on 2026-09-23
-- updated on 2026-09-26

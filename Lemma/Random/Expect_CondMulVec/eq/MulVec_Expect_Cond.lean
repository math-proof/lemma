import Mathlib.Data.Matrix.Mul
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.WithDensity
import sympy.stats.joint_rv
import sympy.Basic


/--
Pull a constant Mathlib matrix–vector product (`*ᵥ` / `Matrix.mulVec`) through
conditional expectation, componentwise.

Renamed out of `Expect_CondDot` (which is reserved for Tensor `@` / `Dot.dot`).

| attributes | lemma |
| :---: | :---: |
| main | Random.Expect_CondMulVec.eq.MulVec_Expect_Cond |
| comm | Random.MulVec_Expect_Cond.eq.Expect_CondMulVec |
-/
@[main, comm]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure γ]
  [Countable α] [MeasurableSingletonClass α]
  {π : MeasureTheory.Measure Ω} {m n : ℕ}
  {a : Ω → α} {s : Ω → γ}
  {f : α → Fin n → ENNReal}
-- given
  (hP : PSpace π (a, s))
  (A : Matrix (Fin m) (Fin n) ENNReal)
  (hf : ∀ i : Fin n, Measurable (fun x : α ↦ f x i))
  («s.bvar» : γ) :
-- imply
  (fun j : Fin m ↦ 𝔼[a: π](Matrix.mulVec A (f a) j | s = «s.bvar»)) =
    Matrix.mulVec A (fun i : Fin n ↦ 𝔼[a: π](f a i | s = «s.bvar»)) := by
-- proof
  ext j
  simp only [Expectation.condRV, expectation_ennreal, Matrix.mulVec, dotProduct]
  rw [MeasureTheory.lintegral_finsetSum (μ := _) (Finset.univ : Finset (Fin n))
    fun i _ => (hf i).const_mul (A j i)]
  refine Finset.sum_congr rfl ?_
  intro i _
  exact MeasureTheory.lintegral_const_mul (A j i) (hf i)


-- created on 2026-09-23
-- updated on 2026-09-26

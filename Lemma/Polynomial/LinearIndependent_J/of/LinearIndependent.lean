import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
import Lemma.Polynomial.Any_Eq_SMul.of.EqWronskian_0.Ne_0
open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial


/--
[rothPolyWronskian_tail_linearIndependent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {k : ℕ} [Field K] [CharZero K]
  (f : Fin (k + 1) → K[X])
-- given
  (hf : LinearIndependent K f) :
-- imply
  LinearIndependent K (fun j : Fin k ↦ wronskian (f 0) (f j.succ)) := by
-- proof
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  let h : K[X] := ∑ j, c j • f j.succ
  have hwr : wronskian (f 0) h = 0 := calc
    _ = ∑ j, c j • wronskian (f 0) (f j.succ) := by
      simp [h, ← wronskianBilin_apply]
    _ = 0 := hc
  obtain ⟨a, ha⟩ := Any_Eq_SMul.of.EqWronskian_0.Ne_0 hwr (hf.ne_zero 0)
  let d : Fin (k + 1) → K := Fin.cons (-a) (fun i ↦ c i)
  have hrel : ∑ i, d i • f i = 0 := by
    rw [Fin.sum_univ_succ]
    simp only [d, Fin.cons_zero, Fin.cons_succ]
    change (-a) • f 0 + h = 0
    rw [ha]
    simp
  have hz := Fintype.linearIndependent_iff.mp hf d hrel j.succ
  simpa [d] using hz


-- created on 2026-10-21

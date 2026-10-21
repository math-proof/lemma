import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
import Lemma.Polynomial.RothPolyJetRows.sub.RothPolyJetRows.of.Le
import Lemma.Polynomial.RothPolyRowDerivative_RothPolyDerivativeRow.eq.RothPolyDerivativeRowAdd_1
open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial


/--
[rothPolyRowDerivative_mem_span](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {k : ℕ} [Field K]
  (f : Fin k → K[X])
  {s : ℕ}
  {v : Fin k → K[X]}
-- given
  (hv : v ∈ Submodule.span K[X] (rothPolyJetRows f s)) :
-- imply
  rothPolyRowDerivative v ∈ Submodule.span K[X] (rothPolyJetRows f (s + 1)) := by
-- proof
  let T := Submodule.span K[X] (rothPolyJetRows f (s + 1))
  have hold : Submodule.span K[X] (rothPolyJetRows f s) ≤ T :=
    Submodule.span_mono (RothPolyJetRows.sub.RothPolyJetRows.of.Le f (Nat.le_succ s))
  apply Submodule.span_induction (R := K[X]) (s := rothPolyJetRows f s)
    (p := fun v _ ↦ rothPolyRowDerivative v ∈ T)
  ·
    rintro _ ⟨n, hn, rfl⟩
    rw [RothPolyRowDerivative_RothPolyDerivativeRow.eq.RothPolyDerivativeRowAdd_1]
    apply Submodule.subset_span
    refine ⟨n + 1, Nat.add_le_add_right hn 1, rfl⟩
  ·
    have hz : rothPolyRowDerivative (0 : Fin k → K[X]) = 0 := by
      ext j
      simp [rothPolyRowDerivative]
    rw [hz]
    apply T.zero_mem
  ·
    intro u w _ _ hu' hw'
    have hadd : rothPolyRowDerivative (u + w) =
        rothPolyRowDerivative u + rothPolyRowDerivative w := by
      ext j
      simp [rothPolyRowDerivative]
    rw [hadd]
    apply T.add_mem hu' hw'
  ·
    intro c w hw hw'
    have hwT : w ∈ T := hold hw
    have hsum : derivative c • w + c • rothPolyRowDerivative w ∈ T :=
      T.add_mem (T.smul_mem _ hwT) (T.smul_mem _ hw')
    convert hsum using 1
    ext j
    simp [rothPolyRowDerivative, derivative_mul]
  ·
    apply hv


-- created on 2026-10-21

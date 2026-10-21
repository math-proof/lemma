import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
import Lemma.Submodule.RothPolyRowDerivative.in.Span_XRothKronHasseJetRowsAdd_1.of.In_Span_XRothKronHasseJetRows
import Lemma.Polynomial.RothPolyRowDerivative_RothPolyDerivativeRow.eq.RothPolyDerivativeRowAdd_1
import Lemma.Fin.EqRothMvHasse0
open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial
open Submodule
open Fin


/--
[rothPolyDerivativeRow_mem_kronHasse_span](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m k : ℕ} (D : ℕ)
  (f : Fin k → MvPolynomial (Fin m) ℚ)
  (s : ℕ) :
-- imply
  rothPolyDerivativeRow (fun j ↦ rothKronecker D (f j)) s ∈
    Submodule.span ℚ[X] (rothKronHasseJetRows D f s) := by
-- proof
  induction s with
  | zero =>
    apply Submodule.subset_span
    refine ⟨0, by simp [rothMvOrder], ?_⟩
    ext j
    simp [rothPolyDerivativeRow, rothKronHasseRow, EqRothMvHasse0]
  | succ s ih =>
    have hder :=
      RothPolyRowDerivative.in.Span_XRothKronHasseJetRowsAdd_1.of.In_Span_XRothKronHasseJetRows D f ih
    rw [RothPolyRowDerivative_RothPolyDerivativeRow.eq.RothPolyDerivativeRowAdd_1] at hder
    simpa [Nat.succ_eq_add_one] using hder


-- created on 2026-10-21

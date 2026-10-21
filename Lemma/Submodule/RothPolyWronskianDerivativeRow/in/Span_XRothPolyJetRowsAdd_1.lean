import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
import Lemma.Submodule.RothPolyRowDerivative.in.Span_XRothPolyJetRowsAdd_1.of.In_Span_XRothPolyJetRows
import Lemma.Submodule.RothPolyWronskianRow.in.Span_XRothPolyJetRows1
open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial
open Submodule


/--
[rothPolyWronskianDerivativeRow_mem_span](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {k : ℕ} [Field K]
  (f : Fin (k + 1) → K[X])
  (n : ℕ) :
-- imply
  rothPolyWronskianDerivativeRow f n ∈
    Submodule.span K[X] (rothPolyJetRows f (n + 1)) := by
-- proof
  induction n with
  | zero =>
    change rothPolyWronskianRow f ∈ Submodule.span K[X] (rothPolyJetRows f 1)
    apply RothPolyWronskianRow.in.Span_XRothPolyJetRows1
  | succ n ih =>
    have hder :=
      RothPolyRowDerivative.in.Span_XRothPolyJetRowsAdd_1.of.In_Span_XRothPolyJetRows f ih
    convert hder using 1
    ·
      ext j
      simp only [rothPolyRowDerivative, rothPolyWronskianDerivativeRow]
      rw [Function.iterate_succ_apply']


-- created on 2026-10-21

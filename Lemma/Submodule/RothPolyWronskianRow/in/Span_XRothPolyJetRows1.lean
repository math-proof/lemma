import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial


/--
[rothPolyWronskianRow_mem_span](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {k : ℕ} [Field K]
  (f : Fin (k + 1) → K[X]) :
-- imply
  rothPolyWronskianRow f ∈ Submodule.span K[X] (rothPolyJetRows f 1) := by
-- proof
  have h0 : rothPolyDerivativeRow f 0 ∈
    Submodule.span K[X] (rothPolyJetRows f 1) :=
    Submodule.subset_span ⟨0, by omega, rfl⟩
  have h1 : rothPolyDerivativeRow f 1 ∈
    Submodule.span K[X] (rothPolyJetRows f 1) :=
    Submodule.subset_span ⟨1, le_rfl, rfl⟩
  have hmem := (Submodule.span K[X] (rothPolyJetRows f 1)).sub_mem
    ((Submodule.span K[X] (rothPolyJetRows f 1)).smul_mem (f 0) h1)
    ((Submodule.span K[X] (rothPolyJetRows f 1)).smul_mem (f 0).derivative h0)
  convert hmem using 1
  ext j
  simp [rothPolyWronskianRow, rothPolyDerivativeRow, wronskian]


-- created on 2026-10-21

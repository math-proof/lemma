import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.Matrix.RoucheCapelli
open scoped Matrix
open MetaMathlibExt


/--
[rouche_capelli](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/RoucheCapelli.lean)
-/
@[path]
private lemma rouche_capelli_eq
  [Fintype n] [Field K]
  {A : Matrix m n K}
  {b : m → K} :
-- imply
  (∃ x : n → K, A *ᵥ x = b) ↔
    A.rank =
    (Matrix.of (fun i => Sum.elim (A i) (fun _ : Fin 1 => b i)) :
    Matrix m (n ⊕ Fin 1) K).rank := by
-- proof
  apply MetaMathlibExt.rouche_capelli A b


-- created on 2026-10-20

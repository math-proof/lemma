import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.Polynomial.HilbertSyzygy
open CategoryTheory Polynomial TensorProduct
open MathlibExt.RingTheory.Polynomial.HilbertSyzygyWanted


/--
[hilbert_syzygy](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Polynomial/HilbertSyzygy.lean)
-/
@[path]
private lemma hilbert_syzygy_eq
  [Field k] [AddCommGroup M]
  {n : ℕ} [Module (MvPolynomial (Fin n) k) M] [Module.Finite (MvPolynomial (Fin n) k) M] :
-- imply
  CategoryTheory.HasProjectiveDimensionLE (ModuleCat.of (MvPolynomial (Fin n) k) M) n := by
-- proof
  apply MathlibExt.RingTheory.Polynomial.HilbertSyzygyWanted.hilbert_syzygy


-- created on 2026-10-20

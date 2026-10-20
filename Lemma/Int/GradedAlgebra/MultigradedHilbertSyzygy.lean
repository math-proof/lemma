import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.GradedAlgebra.MultigradedHilbertSyzygy
open CategoryTheory MvPolynomial
open MetaMathlibExt


/--
[exists_finite_multigraded_free_resolution](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/GradedAlgebra/MultigradedHilbertSyzygy.lean)
-/
@[path]
private lemma exists_finite_multigraded_free_resolution_eq
  {K : Type u} [Field K]
  {n : ℕ}
  {M : Type u} [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M] [Module K M] [Module.Finite (MvPolynomial (Fin n) K) M]
  {targetGraded : MultigradedPolynomialModule K n M} :
-- imply
  ∃ (resolution : CategoryTheory.ProjectiveResolution
    (ModuleCat.of (MvPolynomial (Fin n) K) M))
    (ι : ℕ → Type u)
    (res : MultigradedFreeResolution K n M targetGraded resolution ι)
    (bound : ℕ),
    (∀ i, Finite (ι i)) ∧ ∀ i, bound < i → IsEmpty (ι i) := by
-- proof
  apply MetaMathlibExt.exists_finite_multigraded_free_resolution K n M targetGraded


-- created on 2026-10-20

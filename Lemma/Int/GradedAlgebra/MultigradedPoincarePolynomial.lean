import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.GradedAlgebra.MultigradedPoincarePolynomial
open MetaMathlibExt


/--
[multigradedPoincarePolynomial_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/GradedAlgebra/MultigradedPoincarePolynomial.lean)
-/
@[path]
private lemma multigradedPoincarePolynomial_coeff_eq
  {K : Type u} [Field K]
  {n : ℕ}
  {M : Type u} [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M] [Module K M]
  {targetGraded : MultigradedPolynomialModule K n M}
  {resolution : CategoryTheory.ProjectiveResolution (ModuleCat.of (MvPolynomial (Fin n) K) M)}
  {ι : ℕ → Type u}
  {res : MultigradedFreeResolution K n M targetGraded resolution ι}
  {data : MultigradedBaseChange targetGraded resolution ι res}
  {bound i : ℕ}
  {α : Fin n →₀ Int}
-- given
  (finiteBasis : ∀ i, Finite (ι i))
  (emptyAbove : ∀ i, bound < i → IsEmpty (ι i)) :
-- imply
  (multigradedPoincarePolynomial data bound finiteBasis emptyAbove).coeff (i, α) =
    multigradedBettiNumber data α i := by
-- proof
  apply MetaMathlibExt.multigradedPoincarePolynomial_coeff data bound finiteBasis emptyAbove i α


-- created on 2026-10-20

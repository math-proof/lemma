import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.GradedAlgebra.MultigradedBaseChangedDegreeComplex
open MetaMathlibExt


/--
[MultigradedFreeResolution.multigradedBaseChange_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/GradedAlgebra/MultigradedBaseChangedDegreeComplex.lean)
-/
@[path]
private lemma MultigradedFreeResolution_multigradedBaseChange_nonempty_eq
  {K : Type u} [Field K]
  {n : ℕ}
  {M : Type u} [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M] [Module K M]
  {targetGraded : MultigradedPolynomialModule K n M}
  {resolution : CategoryTheory.ProjectiveResolution (ModuleCat.of (MvPolynomial (Fin n) K) M)}
  {ι : ℕ → Type u}
  {res : MultigradedFreeResolution K n M targetGraded resolution ι}
-- given
  (finiteBasis : ∀ i, Finite (ι i)) :
-- imply
  Nonempty (MultigradedBaseChange targetGraded resolution ι res) := by
-- proof
  apply MetaMathlibExt.MultigradedFreeResolution.multigradedBaseChange_nonempty targetGraded resolution ι res finiteBasis


-- created on 2026-10-20

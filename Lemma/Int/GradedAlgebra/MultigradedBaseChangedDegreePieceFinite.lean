import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.GradedAlgebra.MultigradedBaseChangedDegreePieceFinite
open MetaMathlibExt


/--
[MultigradedFreeResolution.baseChangedDegreePiece_finite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/GradedAlgebra/MultigradedBaseChangedDegreePieceFinite.lean)
-/
@[path]
private lemma MultigradedFreeResolution_baseChangedDegreePiece_finite_eq
  {K : Type u} [Field K]
  {n : Nat}
  {M : Type u} [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M] [Module K M]
  {targetGraded : MultigradedPolynomialModule K n M}
  {resolution : CategoryTheory.ProjectiveResolution (ModuleCat.of (MvPolynomial (Fin n) K) M)}
  {ι : Nat → Type u}
  {res : MultigradedFreeResolution K n M targetGraded resolution ι}
  {α : Fin n →₀ Int}
  {i : Nat} [Finite (ι i)] :
-- imply
  Module.Finite K ↥(baseChangedDegreePiece (K := by
-- proof
  apply MetaMathlibExt.MultigradedFreeResolution.baseChangedDegreePiece_finite K n M targetGraded resolution ι res α i


-- created on 2026-10-20

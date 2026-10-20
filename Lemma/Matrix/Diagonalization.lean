import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.Diagonalization
open MathlibExt.LinearAlgebra.DiagonalizationWanted


/--
[exists_eigenbasis_of_isSemisimple_of_splits](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Diagonalization.lean)
-/
@[path]
private lemma exists_eigenbasis_of_isSemisimple_of_splits_eq
  [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype ι] [DecidableEq ι]
  {f : Module.End K V}
-- given
  (hs : f.IsSemisimple)
  (h : f.charpoly.Splits)
  (hdim : Module.finrank K V = Fintype.card ι) :
-- imply
  ∃ (b : Module.Basis ι K V) (μ : ι → K), ∀ i, f.HasEigenvector (μ i) (b i) := by
-- proof
  apply MathlibExt.LinearAlgebra.DiagonalizationWanted.exists_eigenbasis_of_isSemisimple_of_splits f hs h hdim

/--
[exists_diagonal_similar_of_splits_of_squarefree_minpoly](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Diagonalization.lean)
-/
@[path]
private lemma exists_diagonal_similar_of_splits_of_squarefree_minpoly_eq
  [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype n] [DecidableEq n]
  {A : Matrix n n K}
-- given
  (hsplit : A.charpoly.Splits)
  (hsf : Squarefree (minpoly K (Matrix.toLin' A : Module.End K (n → K)))) :
-- imply
  ∃ P D : Matrix n n K, D.IsDiag ∧ IsUnit P ∧ A = P * D * P⁻¹ := by
-- proof
  apply MathlibExt.LinearAlgebra.DiagonalizationWanted.exists_diagonal_similar_of_splits_of_squarefree_minpoly A hsplit hsf


-- created on 2026-10-20

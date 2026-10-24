import Mathlib
import sympy.Basic
open Matrix Polynomial
open Module


namespace Eigenvalues

/--
[eigenvalue_iff_root_charPoly](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/Eigenvalues.lean)
-/
@[path]
lemma eigenvalue_iff_root_charPoly
  [Fintype n]
  [DecidableEq n]
  [Field F]
  {A : Matrix n n F}
  {μ : F} :
-- imply
  μ ∈ spectrum F A ↔ (Matrix.charpoly A).IsRoot μ :=
-- proof
  Matrix.mem_spectrum_iff_isRoot_charpoly
open Module

end Eigenvalues

namespace Eigenvalues

/--
[eigenvectors_linearIndependent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/Eigenvalues.lean)
-/
@[path]
lemma eigenvectors_linearIndependent
  [Fintype n]
  [DecidableEq n]
  [Field F]
  [CommRing R]
  [IsDomain R]
  [AddCommGroup M]
  [Module R M]
  [IsTorsionFree R M]
  {f : End R M}
  {μ : ι → R}
  {v : ι → M}
-- given
  (hμ : Function.Injective μ)
  (h_eigenvec : ∀ i, f.HasEigenvector (μ i) (v i)) :
-- imply
  LinearIndependent R v :=
-- proof
  f.eigenvectors_linearIndependent' μ hμ v h_eigenvec

end Eigenvalues


-- created on 2026-10-23

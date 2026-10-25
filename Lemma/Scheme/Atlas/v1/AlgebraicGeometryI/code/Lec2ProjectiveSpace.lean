import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.Lec2ProjectiveSpace.Part2
open Formalization
open scoped LinearAlgebra.Projectivization
open MvPolynomial Set


namespace Formalization

/--
[ProjectiveSpace.π_eq_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec2ProjectiveSpace.lean)
-/
@[path]
lemma ProjectiveSpace.π_eq_iff
  [Field k]
  {n : ℕ}
  {v w : PuncturedAffineSpace k n} :
-- imply
  ProjectiveSpace.π k n v = ProjectiveSpace.π k n w ↔ ∃ (a : kˣ), a • (w : Fin (n + 1) → k) = (v : Fin (n + 1) → k) := by
-- proof
  simp only [ProjectiveSpace.π, Projectivization.mk'_eq_mk]
  exact Projectivization.mk_eq_mk_iff k _ _ v.2 w.2

end Formalization

namespace Formalization

/--
[ProjectiveSpace.π_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec2ProjectiveSpace.lean)
-/
@[path]
lemma ProjectiveSpace.π_surjective
  [Field k]
  {n : ℕ} :
-- imply
  Function.Surjective (ProjectiveSpace.π k n) := by
-- proof
  intro p
  induction p using Projectivization.ind with
  | h v hv => exact ⟨⟨v, hv⟩, rfl⟩
section Topology
open MvPolynomial Set

end Formalization


-- created on 2026-10-23

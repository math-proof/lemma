/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/Factorizations/Schur.lean -/

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.RingTheory.PicardGroup

/-!
# Schur decomposition

Every square complex matrix is unitarily similar to an upper-triangular matrix:
`Matrix.exists_unitaryGroup_isUpperTriangular`.
-/

open Matrix
open scoped ComplexOrder

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]

private noncomputable def orderIsoFin (m : Type*) [Fintype m] [DecidableEq m] [LinearOrder m] :
    m ≃o Fin (Fintype.card m) := by
  classical
  let e1 : Fin (Fintype.card m) ≃o ↥(Finset.univ : Finset m) :=
    Finset.orderIsoOfFin Finset.univ (by simp)
  let e2 : ↥(Finset.univ : Finset m) ≃o m := by
    apply StrictMono.orderIsoOfSurjective Subtype.val
    · intro a b hab
      exact hab
    · intro x
      exact ⟨⟨x, Finset.mem_univ x⟩, rfl⟩
  exact (e1.trans e2).symm
end Matrix

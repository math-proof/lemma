/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/Lie/LeviDecomposition.lean -/


import sympy.atlas.Algebra.Lie.LeviDecomposition
import Lemma.Fin.EqSum_SMul.of.Basis

import Mathlib.Algebra.Lie.Semisimple.Basic


namespace MathlibExtTest.Algebra.Lie.LeviDecomposition

-- For a semisimple algebra, the Levi factor supplied by the theorem spans the whole algebra.
example {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] [LieAlgebra.IsSemisimple K L] :
    ∃ S : LieSubalgebra K L, LieAlgebra.IsSemisimple K S ∧
      (S : Submodule K L) = ⊤ := by
  obtain ⟨S, hS, hsum, _⟩ :=
    MathlibExt.Algebra.Lie.LandmarkWanted.levi_decomposition (K := K) (L := L)
  exact ⟨S, hS, by simpa using hsum⟩

-- Weyl's theorem gives every ideal of a semisimple algebra an invariant complement.
example {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] [LieAlgebra.IsSemisimple K L] (I : LieIdeal K L) :
    ∃ J : LieIdeal K L, IsCompl I J := by
  exact LieModule.exists_isCompl_of_isSemisimple I

end MathlibExtTest.Algebra.Lie.LeviDecomposition

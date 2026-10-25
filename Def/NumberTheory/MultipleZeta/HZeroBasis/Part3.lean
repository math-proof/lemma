/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/HZeroBasis.lean -/

import Theorem.NumberTheory.MultipleZeta.WordAlgebra.Part2
import Lemma.Nat.MultipleZeta.WordAlgebra
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Theorem.NumberTheory.MultipleZeta.HZeroBasis.Part2
/-!
# Multiple-zeta word bases

This file records the two substantial basis constructions left after the
proved word-subalgebra interface in
`MathlibExt.NumberTheory.MultipleZeta.WordAlgebra`.
-/


section

namespace MathlibExt.NumberTheory.MultipleZeta.WordAlgebraWanted

open MetaMathlibExt.MultipleZeta

def spanEquivHZero :
    ↥(Submodule.span ℚ (Set.range (fun idx : HZeroIndex => zMonomial idx.val))) ≃ₗ[ℚ]
      ↥hZero where
  toFun x := ⟨x.val, (Subalgebra.mem_toSubmodule hZero).mp (hZero_span_eq ▸ x.property)⟩
  invFun x := ⟨x.val, hZero_span_eq.symm ▸ (Subalgebra.mem_toSubmodule hZero).mpr x.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

end MathlibExt.NumberTheory.MultipleZeta.WordAlgebraWanted
end

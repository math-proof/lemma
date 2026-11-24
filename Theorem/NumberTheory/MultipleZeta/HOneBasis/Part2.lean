module
public import Theorem.NumberTheory.MultipleZeta.WordAlgebra.Part2
public import Theorem.Nat.MultipleZeta.WordAlgebra
public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.DFinsupp
public import Def.NumberTheory.MultipleZeta.HOneBasis.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/HOneBasis.lean -/
/-!
# Hoffman basis of `H^1`

Hoffman monomials indexed by all positive compositions, including the empty
index, form a rational basis of the word subalgebra `hOne` from
`MathlibExt.NumberTheory.MultipleZeta.WordAlgebra`.
-/
section

namespace MetaMathlibExt.MultipleZeta

theorem zWord_indexOfHOneWord (w : FreeMonoid Bool)
    (h : w ∈ wordSubmonoidHOne) : zWord (indexOfHOneWord w) = w := by
  apply FreeMonoid.toList.injective
  have h1 : FreeMonoid.toList (zWord (indexOfHOneWord w)) =
      encodeNatBlocks ((indexOfHOneWord w).entries) := by
    have h2 := toList_zWordPNat (indexOfHOneWord w).pnatEntries
    rw [pnatEntries_val] at h2
    exact h2
  rw [h1]
  change encodeNatBlocks (decodeBlocks (FreeMonoid.toList w)) = FreeMonoid.toList w
  exact encodeNatBlocks_decodeBlocks _ ((mem_HOne_iff_toList w).mp h)

end MetaMathlibExt.MultipleZeta
end

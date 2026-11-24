module
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Int.Star
public import Mathlib.Data.Nat.Choose.Sum
public import Theorem.Combinatorics.Enumerative.LunnonDimensionDecomposition.Part8


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LunnonDimensionDecomposition.lean -/
section

namespace MetaMathlibExt

open scoped BigOperators

noncomputable def fiberEquivProper_aux (d n : ℕ) (A : Finset (Fin d)) :
    fiberSet_aux d n A ≃ properFixedPolycube n A.card where
  toFun := fiberToProper_aux d n A
  invFun := properToFiber_aux d n A
  left_inv := by
    rintro ⟨⟨S, hP, hnS, hC⟩, hsup⟩
    have hz : ∀ x ∈ S, ∀ k : Fin d, k ∉ A → x k = 0 := by
      intro x hx k hkA
      have hkn : k ∉ supportFinset_aux d S := by
        rw [hsup]
        exact hkA
      exact zero_outside_of_not_mem_support_aux d S hC k hkn x hx
    rw [fiberToProper_explicit_aux d n A S hP hnS hC hsup hz]
    apply Subtype.ext
    apply Subtype.ext
    change expandSet_aux2 d A (compressSet_aux2 d A S) = S
    exact expand_compressSet_aux2 d A S hz
  right_inv := by
    rintro ⟨⟨T, hPT, hnT, hCT⟩, hproper⟩
    rw [properToFiber_explicit_aux d n A T hPT hnT hCT hproper]
    apply Subtype.ext
    apply Subtype.ext
    change compressSet_aux2 d A (expandSet_aux2 d A T) = T
    exact compress_expandSet_aux2 d A T

noncomputable def sigmaFiberEquiv_aux (d n : ℕ) :
    (Σ A : Finset (Fin d), fiberSet_aux d n A) ≃ fixedPolycube d n where
  toFun := fun ⟨A, P, _⟩ => P
  invFun := fun P => ⟨supportFinset_aux d P.val, P, rfl⟩
  left_inv := by
    rintro ⟨A, P, h⟩
    subst h
    rfl
  right_inv := by
    intro P
    rfl

end MetaMathlibExt
end

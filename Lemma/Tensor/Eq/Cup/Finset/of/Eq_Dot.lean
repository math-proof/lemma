import sympy.matrices.expressions.permutation
import sympy.vector.Basic
import Lemma.Tensor.GetDot_SwapMatrix.eq.Get
open Tensor


@[main]
private lemma main
  [Semiring α] [CharZero α] [DecidableEq (Tensor α [])]
-- given
  (x y : Tensor α [n])
  (i j : Fin n)
  (h : y = x @ SwapMatrix (α := α) n i j) :
-- imply
  @Finset.image (Fin n) (Tensor α []) _ (fun k => y[k]) Finset.univ = @Finset.image (Fin n) (Tensor α []) _ (fun k => x[k]) Finset.univ := by
-- proof
  let g : Fin n → Tensor α [] := fun k => x[k]
  have hs : (fun k : Fin n => y[k]) = g ∘ Equiv.swap i j := by
    funext k
    apply Eq.trans _ (GetDot_SwapMatrix.eq.Get x i j k)
    rw [h]
    rfl
  rw [hs]
  have key : @Finset.image (Fin n) (Tensor α []) _ (g ∘ Equiv.swap i j) Finset.univ = @Finset.image (Fin n) (Tensor α []) _ g Finset.univ := by
    rw [← Finset.image_image, Finset.image_univ_equiv]
  exact key


-- created on 2020-10-31

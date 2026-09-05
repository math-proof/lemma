import Lemma.Tensor.DotT.eq.Dot
import Lemma.Tensor.EqTT
open Tensor


@[main, comm]
private lemma main
  [CommMagma α] [AddCommMonoid α]
-- given
  (A : Tensor α [n])
  (X : Tensor α [n, n]) :
-- imply
  A @ Xᵀ = X @ A := by
-- proof
  apply Eq.trans (DotT.eq.Dot Xᵀ A).symm
  exact congrArg (fun t => t @ A) (EqTT X)


@[main, comm]
private lemma resize
  [CommMagma α] [AddCommMonoid α]
-- given
  (A : Tensor α [n'])
  (X : Tensor α [n, n]) :
-- imply
  A @ Xᵀ = X @ A := by
-- proof
  apply Eq.trans (DotT.eq.Dot.resize Xᵀ A).symm
  exact congrArg (fun t => t @ A) (EqTT X)


-- created on 2026-09-03

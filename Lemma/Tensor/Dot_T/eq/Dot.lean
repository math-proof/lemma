import Lemma.Tensor.DotT.eq.Dot
import Notation.Data.Tensor.Permute
import Lemma.Tensor.EqTT
import Instance.Data.Vector.Basic.Dot
open Tensor


@[path, comm]
private lemma main
  [CommMagma α] [AddCommMonoid α]
-- given
  (A : Tensor α [n])
  (X : Tensor α [n, n]) :
-- imply
  A ⬝ᵥ Xᵀ = X ⬝ᵥ A := by
-- proof
  apply Eq.trans (DotT.eq.Dot Xᵀ A).symm
  exact congrArg (fun t : Tensor α [n, n] => t ⬝ᵥ A) (EqTT X)


@[path, comm]
private lemma resize
  [CommMagma α] [AddCommMonoid α]
-- given
  (A : Tensor α [n'])
  (X : Tensor α [n, n]) :
-- imply
  A ⬝ᵥ Xᵀ = X ⬝ᵥ A := by
-- proof
  apply Eq.trans (DotT.eq.Dot.resize Xᵀ A).symm
  exact congrArg (fun t : Tensor α [n, n] => t ⬝ᵥ A) (EqTT X)


-- created on 2026-09-03

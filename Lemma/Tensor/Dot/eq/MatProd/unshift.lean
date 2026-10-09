import Lemma.Tensor.DotDot.eq.Dot_Dot
import Lemma.Tensor.EqDotEye
import Lemma.Tensor.EqDot_Eye
import Lemma.Tensor.MatProd.eq.DotMatProd
open Tensor


@[path]
private lemma main
  [Semiring α] [CharZero α]
  {m : ℕ}
  (f : Fin (n + 1) → Tensor α [m, m]) :
-- imply
  (f 0) @ matProd n (fun j => f j.succ) = matProd (n + 1) f := by
-- proof
  induction n with
  | zero =>
    rw [MatProd.eq.DotMatProd]
    simp only [matProd]
    rw [EqDot_Eye, EqDotEye]
    rfl
  | succ n ih =>
    let q : Fin n → Tensor α [m, m] := fun i => f i.castSucc.succ
    let a : Tensor α [m, m] := f (Fin.last n).succ
    have hassoc := DotDot.eq.Dot_Dot
      (l := m) (m := m) (n := m) (o := m)
      (L := f 0) (M := matProd n q) (N := a)
    have h₁ : (f 0) @ matProd (n + 1) (fun j => f j.succ) =
        (f 0) @ ((matProd n q) @ a) := by
      rw [MatProd.eq.DotMatProd]
      rfl
    have h₂ :
      (f 0) @ ((matProd n q) @ a) = ((f 0) @ matProd n q) @ a :=
        hassoc.symm
    apply Eq.trans h₁
    apply Eq.trans h₂
    apply Eq.trans
    · exact congrArg (fun X : Tensor α [m, m] => X @ a) (ih (fun i => f i.castSucc))
    · exact (MatProd.eq.DotMatProd (f := f)).symm


-- created on 2026-10-09

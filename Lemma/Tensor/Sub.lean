import Lemma.Tensor.DataAdd.eq.AddDataS
import Lemma.Tensor.DataNeg.eq.NegData
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.GetAdd.eq.AddGetS
import Lemma.Vector.GetNeg.eq.NegGet
import Lemma.Vector.GetSub.eq.SubGet
import sympy.tensor.tensor
open Tensor Vector


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.Sub |
| comm | Tensor.Sub.comm |
-/
@[main, comm]
private lemma main
  [SubNegMonoid α]
-- given
  (X Y : Tensor α []) :
-- imply
  X - Y = Sub.sub X Y := by
-- proof
  have h : X - Y = Add.add X (-Y) := by
    apply Eq.of.EqDataS
    ext i
    have hi : (i : ℕ) = 0 := Nat.lt_one_iff.mp i.isLt
    change (X.data - Y.data[0]).get i = (Add.add X (-Y)).data.get i
    erw [GetSub.eq.SubGet.fin (x := X.data) (a := Y.data[0]) (i := i)]
    erw [DataAdd.eq.AddDataS X (-Y)]
    erw [DataNeg.eq.NegData Y]
    erw [GetAdd.eq.AddGetS.fin (a := X.data) (b := -Y.data) (i := i)]
    erw [GetNeg.eq.NegGet.fin (x := Y.data) (i := i)]
    rw [sub_eq_add_neg (X.data.get i) Y.data[0]]
    apply congrArg (fun t => X.data.get i + -t)
    apply congrArg Y.data.get
    apply Fin.ext
    simp [hi]
  exact h.trans (sub_eq_add_neg X Y).symm


-- created on 2026-09-02

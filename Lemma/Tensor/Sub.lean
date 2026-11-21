import Instance.Data.Tensor.Tensor.Part2
open Tensor Vector


/--
| attributes | lemma |
| :---: | :---: |
| path | Tensor.Sub |
| comm | Tensor.Sub.comm |
-/
@[path, comm]
private lemma main
  [SubNegMonoid α]
-- given
  (X Y : Tensor α []) :
-- imply
  X - Y = Sub.sub X Y := by
-- proof
  apply Eq.trans _ (sub_eq_add_neg X Y).symm
  apply Eq.of.EqDataS
  ext i
  have hi : (i : ℕ) = 0 := Nat.lt_one_iff.mp i.isLt
  change (X.data - Y.data[0]).get i = (Add.add X (-Y)).data.get i
  change (X.data.map fun x => x - Y.data[0]).get i = _
  rw [List.Vector.get_map]
  erw [DataAdd.eq.AddDataS X (-Y)]
  erw [DataNeg.eq.NegData Y]
  erw [GetAdd.eq.AddGetS.fin (a := X.data) (b := -Y.data) (i := i)]
  erw [GetNeg.eq.NegGet.fin (x := Y.data) (i := i)]
  rw [sub_eq_add_neg (X.data.get i) Y.data[0]]
  apply congrArg (fun t => X.data.get i + -t)
  apply congrArg Y.data.get
  apply Fin.ext
  simp [hi]


-- created on 2026-09-02
-- updated on 2026-11-20

import sympy.tensor.Basic
open Bool Nat Int List Lean Tensor

def Tensor.rotate (X : Tensor α s) (i : ℕ): Tensor α (s.rotate i) :=
  let k := i % s.length
  let data : List.Vector α (List.drop k s ++ List.take k s).prod := cast (by simp) (X.data.splitAt k).transpose.flatten
  ⟨cast (by rw [AppendDrop__Take.eq.Rotate s i]) data⟩

def Tensor.permuteHead (X : Tensor α s) (size : ℕ) : Tensor α ((s.take size).rotate 1 ++ s.drop size) :=
  let X : Tensor _ (s.take size) := ⟨X.data.splitAt size⟩
  let X := X.rotate 1
  ⟨cast (by simp_all) X.data.flatten⟩

def Tensor.permuteTail (X : Tensor α s) (size : ℕ) : Tensor α (s.take (s.length - size) ++ (s.drop (s.length - size)).rotate (size ⊓ s.length - 1)) :=
  let data : List.Vector (List.Vector α ((s.drop (s.length - size)).rotate (size ⊓ s.length - 1)).prod) (s.take (s.length - size)).prod := (X.data.splitAt (s.length - size)).map fun data =>
    let X : Tensor _ (s.drop (s.length - size)) := ⟨data⟩
    (X.rotate (size ⊓ s.length - 1)).data
  ⟨cast (by simp_all) data.flatten⟩

/--
[torch.permute](https://docs.pytorch.org/docs/stable/generated/torch.permute.html)
-/
def Tensor.permute (X : Tensor α s) (i : Fin s.length) (d : ℤ) : Tensor α (s.permute i d) :=
  match d with
  | .ofNat d =>
    match d with
    | 0 =>
      cast (by simp [EqPermute]) X
    | d + 1 =>
      if h : i.val = 0 then
        have := Permute.eq.AppendRotateTake___Drop.of.EqVal_0 h d.succ
        cast (by simp_all) (X.permuteHead (d + 2))
      else
        have := ProdPermute.eq.MulProd_ProdAppend i d.succ
        ⟨cast (by simp_all) ((X.data.splitAt i).map fun data => ((⟨data⟩ : Tensor α (s.drop i)).permuteHead (d + 2)).data).flatten⟩
  | .negSucc d =>
    if h : i.val = s.length - 1 then
      have := Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1 h d.succ
      cast (by simp_all [NegSucc.eq.NegAdd_1]) (X.permuteTail (d + 2))
    else
      have h1 := ProdPermute__Neg.eq.MulProd_ProdDrop i d.succ
      have h2 : (d + 2) ⊓ (↑i + 1) - 1 = (d + 1) ⊓ ↑i := by omega
      ⟨cast (by simp_all [NegSucc.eq.NegCoeAdd_1]) ((⟨X.data.splitAt (i + 1)⟩ : Tensor (List.Vector α (s.drop (i + 1)).prod) (s.take (i + 1))).permuteTail (d + 2)).data.flatten⟩

/--
[torch.transpose](https://docs.pytorch.org/docs/stable/generated/torch.transpose.html)
-/
def Tensor.transpose (X : Tensor α s) (i j : ℕ) : Tensor α (s.swap i j) :=
  if h_eq : i = j then
    cast (by simp_all [List.swap_self]) X
  else if h : i ≥ s.length ∨ j ≥ s.length then
    cast (by obtain hi | hj := h <;> simp_all) X
  else
    have h : i ⊔ j < s.length := by
      simp_all
    let args : ℕ × ℕ := if i > j then ⟨j, i⟩ else ⟨i, j⟩
    have h_ite : (args : ℕ × ℕ) = if i > j then ⟨j, i⟩ else ⟨i, j⟩ := rfl
    let ⟨i, j⟩ := args
    have h_lt := Lt.of.Prod.eq.IteGt.Ne h_eq h_ite
    have h : i ⊔ j < s.length := by
      simp_all [Max.of.Prod.eq.IteGt h_ite]
    have h_i : i < s.length := by
      simp_all
    have h_j : j < s.length := by
      simp_all
    let d := j - i
    have h_j' : j < (s.permute ⟨i, h_i⟩ (d - 1)).length := by
      simpa
    cast
      (by
        apply UFn.of.Eq (f := Tensor α)
        rw [PermutePermute.eq.Swap.of.Lt.GtLength h_j h_lt]
        rw [Swap.of.Prod.eq.IteGt h_ite]
      )
      ((X.permute ⟨i, h_i⟩ (d - 1)).permute ⟨j, h_j'⟩ (-d))

def Tensor.T (X : Tensor α s) : Tensor α (s.swap (s.length - 2) (s.length - 1)) :=
  X.transpose (s.length - 2) (s.length - 1)

postfix:1024 "ᵀ" => Tensor.T

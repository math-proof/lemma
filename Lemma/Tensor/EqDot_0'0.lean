import Lemma.Tensor.EqSum0_0
import Lemma.Tensor.EqUnsqueeze0'0
import Lemma.Tensor.EqStack_0'0
import Lemma.Tensor.EqData0'0
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.Repeat.of.Eq
import Lemma.Tensor.Sum.of.Eq
import Lemma.Tensor.Unsqueeze.of.Eq
import Lemma.Tensor.GetOfVector.eq.Get
import Lemma.Vector.EqSplitAt0_0
import Lemma.Vector.EqGet0_0
import Lemma.Vector.Flatten0.eq.Zero
import Lemma.Vector.EqReplicate0_0
import Lemma.Vector.EqCast_0'0.of.Eq
import Lemma.Vector.EqAppend0S0
import Lemma.Vector.EqGetRange
import Lemma.List.Set_0.eq.Cons_Tail.of.GtLength_0
import Lemma.List.SetAppend.eq.Append_Set.of.LeLength
import sympy.matrices.expressions.matmul
open Tensor Vector


-- `replicate n 0 = 0` normalization lemma (reverse of Zero.eq.Replicate)
private lemma vrep0 [Zero α] : List.Vector.replicate n (0 : α) = 0 := rfl

-- `Tensor.mk 0 = 0`
private lemma tmk0 [Zero α] : (⟨0⟩ : Tensor α s) = 0 := rfl

-- cast of a zero vector along an explicit length equality
private lemma vcast0_heq
  [Zero α]
  {n n' : ℕ}
  (h : List.Vector α n = List.Vector α n')
  (hn : n = n') :
  cast h (0 : List.Vector α n) = (0 : List.Vector α n') := by
  subst hn
  rw [cast_eq h]

-- cast of a zero tensor along an explicit shape equality
private lemma tcast0_heq
  [Zero α]
  {s s' : List ℕ}
  (h : Tensor α s = Tensor α s')
  (hs : s = s') :
  cast h (0 : Tensor α s) = (0 : Tensor α s') := by
  subst hs
  rw [cast_eq h]

-- ℕ-indexed getElem of a zero vector
private lemma vget0_nat
  [Zero α]
  {n : ℕ}
  (i : Fin n) :
  (0 : List.Vector α n)[(i : ℕ)] = 0 := by
  simpa using Vector.EqGet0_0 i

-- Fin-indexed `get` of a zero vector
private lemma vget0_fin
  [Zero α]
  {n : ℕ}
  (i : Fin n) :
  List.Vector.get (0 : List.Vector α n) i = 0 := by
  rw [← vrep0]
  exact List.Vector.get_replicate _ _

-- mapping a zero-preserving function over a zero vector gives zero
private lemma vmap0'0
  [Zero γ] [Zero δ]
  {n : ℕ}
  (f : γ → δ) (hf : f 0 = 0) :
  (0 : List.Vector γ n).map f = 0 := by
  have hmap : (0 : List.Vector γ n).map f = List.Vector.replicate n (f 0) := by
    rw [← vrep0]
    apply Subtype.ext
    simp [List.Vector.map, List.Vector.replicate, List.map_replicate]
  rw [hmap, hf, vrep0]

-- `map₂ f u 0 = 0` whenever `f b 0 = 0` for all `b`
private lemma vmap2_0s0
  [Zero γ] [Zero δ]
  {n : ℕ}
  {u : List.Vector β n}
  (f : β → γ → δ)
  (hf : ∀ b, f b 0 = 0) :
  List.Vector.map₂ f u (0 : List.Vector γ n) = 0 := by
  ext i
  rw [List.Vector.get_map₂]
  have hz1 : (List.Vector.get (0 : List.Vector γ n) i) = 0 := by
    rw [← vrep0]
    exact List.Vector.get_replicate _ _
  have hz2 : (List.Vector.get (0 : List.Vector δ n) i) = 0 := by
    rw [← vrep0]
    exact List.Vector.get_replicate _ _
  rw [hz1, hz2]
  exact hf _

private lemma vrepeat0'0
  [Zero α]
  {n m : ℕ} :
  (0 : List.Vector α n).repeat m = 0 := by
  simp only [List.Vector.repeat, ← Vector.Zero.eq.Replicate]
  exact Vector.Flatten0.eq.Zero m n

private lemma vresize0'0
  [Zero α]
  {n n' : ℕ} :
  (0 : List.Vector α n).resize n' = 0 := by
  simp [List.Vector.resize, vrepeat0'0, Vector.EqAppend0S0]
  rw [vcast0_heq _ (Nat.EqAddMulDiv n' n)]

private lemma vtranspose0'0
  [Zero α]
  {n m : ℕ} :
  (0 : List.Vector (List.Vector α n) m).transpose = 0 := by
  ext j i
  simp [List.Vector.transpose, vget0_nat, vget0_fin]

-- slicing a zero vector gives zero
private lemma vgetSlice0'0
  [Zero α]
  {n : ℕ}
  (s : Slice) :
  (0 : List.Vector α n).getSlice s = 0 := by
  simp [List.Vector.getSlice, vget0_nat, List.Vector.indices,
    List.Vector.map, List.map_const', List.LengthRange.eq.Length]
  apply Subtype.ext
  simp [Vector.Zero.eq.Replicate, List.Vector.replicate, Subtype.coe_mk]

-- `OfVector` of a zero vector of tensors is zero
private lemma tOfVector0'0
  [Zero α]
  {s : List ℕ} {n : ℕ} :
  Tensor.OfVector (0 : List.Vector (Tensor α s) n) = 0 := by
  apply Eq.of.EqDataS
  simp only [Tensor.OfVector]
  rw [vmap0'0 (Tensor.data : Tensor α s → List.Vector α s.prod) (by rfl)]
  exact Vector.Flatten0.eq.Zero n s.prod

-- `toVector` of a zero tensor is zero
private lemma tToVector0'0
  [Zero α]
  {s : List ℕ} :
  (0 : Tensor α s).toVector = 0 := by
  have hf : (fun v : List.Vector α (s.drop 1).prod =>
      (⟨cast (by simp) v⟩ : Tensor α s.tail)) 0 = 0 := by
    show (⟨cast _ (0 : List.Vector α (s.drop 1).prod)⟩ : Tensor α s.tail) = 0
    rw [vcast0_heq _ (by simp)]
    exact tmk0
  simp only [Tensor.toVector, EqData0'0, Vector.EqSplitAt0_0]
  rw [vmap0'0 _ hf]
  rw [vcast0_heq _ (by rw [List.ProdTake_1.eq.HeadD_1])]

-- `toVector` of a cast zero tensor is zero
private lemma tcastToVector0'0
  [Zero α]
  {s s' : List ℕ}
  (h : Tensor α s = Tensor α s')
  (hs : s = s') :
  (cast h (0 : Tensor α s)).toVector = 0 := by
  subst hs
  rw [cast_eq h]
  exact tToVector0'0

private lemma resize0'0
  [Zero α]
  {s : List ℕ}
  (d : Fin s.length) (n : ℕ) :
  (0 : Tensor α s).resize d n = 0 := by
  apply Eq.of.EqDataS
  simp only [Tensor.resize, EqData0'0, Vector.EqSplitAt0_0]
  rw [vmap0'0
    (fun x : List.Vector α (s.drop d).prod =>
      x.resize (n * (s.drop d.succ).prod)) vresize0'0]
  simp [Vector.Flatten0.eq.Zero]
  rw [vcast0_heq _ (by simp [List.ProdSet.eq.MulProd_Mul_Prod.of.GtLength])]

-- `toVector` of a head-resized zero tensor is zero
private lemma resizeToVector0'0
  [Zero α]
  {s : List ℕ}
  (h : s.length > 0)
  (n : ℕ) :
  ((0 : Tensor α s).resize ⟨0, h⟩ n).toVector = 0 := by
  rw [resize0'0 ⟨0, h⟩ n]
  exact tToVector0'0

private lemma reshape0'0
  [Zero α]
  {s s' : List ℕ}
  (h : s.prod ∣ s'.prod) :
  (0 : Tensor α s).reshape s' h = 0 := by
  apply Eq.of.EqDataS
  simp only [Tensor.reshape, EqData0'0, vrepeat0'0]
  rw [vcast0_heq _ (Nat.EqMulDiv.of.Dvd h)]

-- `cast → resize → cast` of a zero tensor stays zero
private lemma castResizeCast0'0
  [Zero α]
  {s₁ s₂ s₃ : List ℕ}
  (d : Fin s₂.length) (n : ℕ)
  (h1 : Tensor α s₁ = Tensor α s₂) (hs1 : s₁ = s₂)
  (h2 : Tensor α (s₂.set d n) = Tensor α s₃) (hs2 : s₂.set d n = s₃) :
  cast h2 ((cast h1 (0 : Tensor α s₁)).resize d n) = 0 :=
  (congrArg (fun t => cast h2 (t.resize d n)) (tcast0_heq h1 hs1)).trans
    ((congrArg (cast h2) (resize0'0 d n)).trans (tcast0_heq h2 hs2))

-- `resize → reshape` of a zero tensor stays zero
private lemma resizeReshape0'0
  [Zero α]
  {s₁ s₃ : List ℕ}
  (d : Fin s₁.length) (n : ℕ) (hdiv : (s₁.set d n).prod ∣ s₃.prod) :
  ((0 : Tensor α s₁).resize d n).reshape s₃ hdiv = 0 :=
  (congrArg (fun (t : Tensor α (s₁.set d n)) => t.reshape s₃ hdiv)
    (resize0'0 d n)).trans
    (reshape0'0 hdiv)

private lemma select0'0
  [Zero α]
  {s : List ℕ}
  (o : Fin s.length) (i : Fin s[o]) :
  (0 : Tensor α s).select o i = 0 := by
  apply Eq.of.EqDataS
  simp only [Tensor.select, EqData0'0, Vector.EqSplitAt0_0]
  simp [vgetSlice0'0, Vector.Flatten0.eq.Zero]
  exact vcast0_heq _
    (List.MulLengthSlice.eq.ProdEraseIdx.of.GtGet.GtLength.simp o.isLt i.isLt)

private lemma repeat0'0
  [Zero α]
  {s : List ℕ}
  (d : Fin s.length) (n : ℕ) :
  (0 : Tensor α s).repeat d n = 0 := by
  apply Eq.of.EqDataS
  simp only [Tensor.repeat, EqData0'0, Vector.EqSplitAt0_0]
  rw [vmap0'0 (fun x : List.Vector α (s.drop d).prod => x.repeat n) vrepeat0'0]
  simp [Vector.Flatten0.eq.Zero]
  rw [vcast0_heq _ (by simp [List.ProdSet__Mul_Get.eq.MulProd_Mul_Prod.of.GtLength])]

private lemma rotate0'0
  [Zero α]
  {s : List ℕ}
  (k : ℕ) :
  (0 : Tensor α s).rotate k = 0 := by
  apply Eq.of.EqDataS
  simp only [Tensor.rotate]
  simp (config := { zeta := true }) [EqData0'0, Vector.EqSplitAt0_0,
    vtranspose0'0, Vector.Flatten0.eq.Zero]
  rw [vcast0_heq _ (by
    rw [← List.prod_append, List.AppendDrop__Take.eq.Rotate s k])]

private lemma permuteHead0'0
  [Zero α]
  {s : List ℕ}
  (size : ℕ) :
  (0 : Tensor α s).permuteHead size = 0 := by
  apply Eq.of.EqDataS
  simp [Tensor.permuteHead, EqData0'0, Vector.EqSplitAt0_0,
    tmk0, rotate0'0, Vector.Flatten0.eq.Zero]
  rw [vcast0_heq _ (by simp [List.prod_append])]

private lemma permuteTail0'0
  [Zero α]
  {s : List ℕ}
  (size : ℕ) :
  (0 : Tensor α s).permuteTail size = 0 := by
  apply Eq.of.EqDataS
  simp only [Tensor.permuteTail, EqData0'0, Vector.EqSplitAt0_0]
  rw [vmap0'0 (fun data => ((⟨data⟩ : Tensor α _).rotate _).data)
        (by simp [tmk0, rotate0'0, EqData0'0])]
  simp [Vector.Flatten0.eq.Zero]
  rw [vcast0_heq _ (by simp [List.prod_append])]

private lemma permute0'0
  [Zero α]
  {s : List ℕ}
  (i : Fin s.length) (d : ℤ) :
  (0 : Tensor α s).permute i d = 0 := by
  cases d with
  | ofNat d =>
    cases d with
    | zero =>
      simp only [Tensor.permute]
      rw [tcast0_heq _ (List.EqPermute i).symm]
    | succ d =>
      simp (config := { zeta := true }) only [Tensor.permute]
      split_ifs with h_i0
      · -- i.val = 0
        rw [permuteHead0'0]
        rw [tcast0_heq _
          ((List.Permute.eq.AppendRotateTake___Drop.of.EqVal_0
            h_i0 (d + 1)).symm)]
      · -- i.val ≠ 0
        simp only [EqData0'0, Vector.EqSplitAt0_0, vmap0'0, tmk0,
          permuteHead0'0, Vector.Flatten0.eq.Zero]
        apply Eq.of.EqDataS
        exact vcast0_heq _
          (List.ProdPermute.eq.MulProd_ProdAppend i (d + 1)).symm
  | negSucc d =>
    simp (config := { zeta := true }) only [Tensor.permute]
    split_ifs with h_il
    · -- i.val = s.length - 1
      rw [permuteTail0'0]
      rw [tcast0_heq _ (by
        rw [Int.NegSucc.eq.NegAdd_1]
        exact (List.Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1
          h_il (d + 1)).symm)]
    · -- i.val ≠ s.length - 1
      simp only [EqData0'0, Vector.EqSplitAt0_0, tmk0,
        permuteTail0'0, Vector.Flatten0.eq.Zero]
      apply Eq.of.EqDataS
      exact vcast0_heq _ (by
        rw [Int.NegSucc.eq.NegCoeAdd_1]
        exact (List.ProdPermute__Neg.eq.MulProd_ProdDrop i (d + 1)).symm)

private lemma transpose0'0
  [Zero α]
  {s : List ℕ}
  (i j : ℕ) :
  (0 : Tensor α s).transpose i j = 0 := by
  simp (config := { zeta := true }) only [Tensor.transpose]
  split_ifs
  · rw [tcast0_heq _ (by rw [‹i = j›]; simp [List.swap_self])]
  · rw [tcast0_heq _ (by obtain hi | hj := ‹_› <;> simp_all)]
  · -- else branch, i > j: the inner args if selects ⟨j, i⟩
    rw [permute0'0, permute0'0]
    rw [tcast0_heq _ (by
      let i' := (if i > j then (j, i) else (i, j)).1
      let j' := (if i > j then (j, i) else (i, j)).2
      have h_ite : (⟨i', j'⟩ : ℕ × ℕ) = if i > j then ⟨j, i⟩ else ⟨i, j⟩ := rfl
      rw [← List.Swap.eq.PermutePermute.of.Lt.GtLength
        (s := s) (i := i') (j := j')
        (by show s.length > (if i > j then (j, i) else (i, j)).2
            split_ifs; omega)
        (Nat.Lt.of.Prod.eq.IteGt.Ne ‹i ≠ j› h_ite)]
      exact List.Swap.of.Prod.eq.IteGt h_ite s)]
  · -- else branch, ¬ i > j (i.e. i < j): the inner args if selects ⟨i, j⟩
    rw [permute0'0, permute0'0]
    rw [tcast0_heq _ (by
      let i' := (if i > j then (j, i) else (i, j)).1
      let j' := (if i > j then (j, i) else (i, j)).2
      have h_ite : (⟨i', j'⟩ : ℕ × ℕ) = if i > j then ⟨j, i⟩ else ⟨i, j⟩ := rfl
      rw [← List.Swap.eq.PermutePermute.of.Lt.GtLength
        (s := s) (i := i') (j := j')
        (by show s.length > (if i > j then (j, i) else (i, j)).2
            split_ifs; omega)
        (Nat.Lt.of.Prod.eq.IteGt.Ne ‹i ≠ j› h_ite)]
      exact List.Swap.of.Prod.eq.IteGt h_ite s)]

private lemma tT0'0
  [Zero α]
  {s : List ℕ} :
  (0 : Tensor α s).T = 0 := by
  simp [Tensor.T, transpose0'0]

private lemma mulS0'0
  [MulZeroClass α]
  {s : List ℕ}
  (X : Tensor α s) :
  X * (0 : Tensor α s) = 0 := by
  apply Eq.of.EqDataS
  ext i
  simp [EqData0'0, Vector.Zero.eq.Replicate, List.Vector.get_replicate]

private lemma smul0'0
  [MulZeroClass α]
  {s : List ℕ}
  (a : α) :
  a * (0 : Tensor α s) = 0 := by
  apply Eq.of.EqDataS
  ext i
  simp [HMul.hMul, EqData0'0, Vector.Zero.eq.Replicate,
    List.Vector.get_replicate]
  exact MulZeroClass.mul_zero a

private lemma mul0'0_s
  [MulZeroClass α]
  {s : List ℕ}
  (X : Tensor α s) :
  X * (0 : α) = 0 := by
  apply Eq.of.EqDataS
  ext i
  simp [HMul.hMul, EqData0'0, Vector.Zero.eq.Replicate,
    List.Vector.get_replicate]
  exact MulZeroClass.mul_zero (X.data.get i)

private lemma bmm0'0
  [NonUnitalNonAssocSemiring α]
  {batch_size : List ℕ} {m k n : ℕ}
  (X : Tensor α (batch_size ++ [m, k])) :
  X.bmm (0 : Tensor α (batch_size ++ [k, n])) = 0 := by
  simp only [Tensor.bmm, tT0'0]
  rw [tcast0_heq _ (by simp [List.SwapAppend.eq.Append_Swap.of.LeLength.LeLength])]
  simp only [EqUnsqueeze0'0]
  rw [tcast0_heq _ (by simp [List.InsertIdxAppend.eq.Append_InsertIdx.of.LeLength])]
  simp only [repeat0'0]
  rw [tcast0_heq _ (by simp)]
  simp only [mulS0'0, EqSum0_0]
  rw [tcast0_heq _ (by simp [List.EraseIdxAppend.eq.Append_EraseIdx.of.LeLength])]

-- tensor times a scalar read out of a zero tensor
private lemma mul0'0_getElem
  [MulZeroClass α]
  {s s' : List ℕ}
  (X : Tensor α s)
  {i : Fin s'.prod} :
  X * (0 : Tensor α s').data[i] = 0 := by
  apply Eq.of.EqDataS
  ext j
  simp [HMul.hMul, EqData0'0, vget0_nat i, vget0_fin j]
  exact MulZeroClass.mul_zero (X.data.get j)

private lemma matmul0'0
  [NonUnitalNonAssocSemiring α]
  {s s' : List ℕ} {m t k : ℕ}
  (X : Tensor α (s ++ [m, t]))
  (h : s.length = s'.length) :
  X.matmul (0 : Tensor α (s' ++ [t, k])) h = 0 := by
  induction s generalizing s' with
  | nil =>
    cases s' with
    | nil =>
      unfold Tensor.matmul
      exact bmm0'0 X
    | cons =>
      simp at h
  | cons n s ih =>
    cases s' with
    | nil =>
      simp at h
    | cons n' s' =>
      unfold Tensor.matmul
      simp (config := { zeta := true }) only []
      have h_v : List.Vector.map₂
          (fun X Y => Tensor.matmul X Y (by simp at h; omega))
          ((X.resize ⟨0, by simp⟩ (n ⊔ n')).toVector)
          (((0 : Tensor α (n' :: s' ++ [t, k])).resize ⟨0, by simp⟩ (n ⊔ n')).toVector) = 0 := by
        rw [resizeToVector0'0 (by simp) (n ⊔ n')]
        exact vmap2_0s0 _
          (fun (Xb : Tensor α (s ++ [m, t])) =>
            ih Xb (by simp at h; omega))
      have h_tail : s.length = s'.length := by simp at h; omega
      have hp : n ⊔ n' :: (broadcast_shape s s' ++ [m, k]) =
          broadcast_shape (n :: s) (n' :: s') ++ [m, k] := by
        simp [broadcast_shape]
        split_ifs
        · simp_all
        · simp_all
        · simp [List.zipWith_cons_cons]
      have h_after : cast (congrArg (Tensor α) hp)
          (Tensor.OfVector
            (0 : List.Vector (Tensor α (broadcast_shape s s' ++ [m, k])) (n ⊔ n'))) =
          (0 : Tensor α (broadcast_shape (n :: s) (n' :: s') ++ [m, k])) := by
        rw [tOfVector0'0]
        exact tcast0_heq _ hp
      exact (congrArg
        (fun v => cast (congrArg (Tensor α) hp) (Tensor.OfVector v)) h_v).trans h_after

private lemma tensordot0'0
  [NonUnitalNonAssocSemiring α]
  {s s' : List ℕ} {m n k : ℕ}
  (X : Tensor α (s ++ [m, n])) :
  X.tensordot (0 : Tensor α (s' ++ [n, k])) = 0 := by
  unfold Tensor.tensordot
  split_ifs
  · simp (config := { zeta := true }) only []
    rw [matmul0'0 _ (by
      rw [List.length_append, List.length_take]; omega)]
    rw [tcast0_heq _ (by
      simp [broadcast_shape]
      split_ifs with h_l h_u
      · grind
      · grind
      · simp
        rw [List.Append_Append.eq.AppendAppend]
        apply List.Append.of.Eq
        rw [List.ZipWith_Append.eq.AppendZipWithS]
        apply List.Append.of.Eq
        simp)]
  · simp (config := { zeta := true }) only []
    simp only [reshape0'0]
    rw [matmul0'0 _ (by
      rw [List.length_append, List.length_take]; omega)]
    rw [tcast0_heq _ (by
      simp [broadcast_shape]
      split_ifs with h_l h_u
      · grind
      · grind
      · simp
        rw [List.Append_Append.eq.AppendAppend]
        apply List.Append.of.Eq
        rw [List.ZipWith__Append.eq.AppendZipWithS]
        apply List.Append.of.Eq
        simp)]
  · rw [matmul0'0 _ (by omega)]

-- einsum with rank 0 on the left and zero on the right
private lemma dot0_0
  [NonUnitalNonAssocSemiring α]
  {s' : List ℕ}
  (X : Tensor α []) :
  X @ (0 : Tensor α s') = (0 : Tensor α (Tensor.matmul_shape [] s')) := by
  show Tensor.einsum X (0 : Tensor α s') = _
  unfold Tensor.einsum
  rw [dif_pos (by simp)]
  rw [smul0'0 _]
  exact tcast0_heq _ (by simp [Tensor.matmul_shape])

-- einsum with rank 1 on the left, rank ≥ 2 zero on the right
private lemma dot1_cons_0
  [NonUnitalNonAssocSemiring α]
  {n kk0 : ℕ} {rest : List ℕ}
  (X : Tensor α [n]) (n' : ℕ) :
  Tensor.einsum X (0 : Tensor α (n' :: kk0 :: rest)) =
    (0 : Tensor α (Tensor.matmul_shape [n] (n' :: kk0 :: rest))) := by
  unfold Tensor.einsum
  rw [dif_neg (by simp), dif_neg (by simp), dif_pos (by simp)]
  simp (config := { zeta := true }) only []
  rw [dif_neg (by simp)]
  let bs' := (n' :: kk0 :: rest).take ((n' :: kk0 :: rest).length - 2)
  let nn1 := (n' :: kk0 :: rest)[rest.length]
  let nn := n ⊔ nn1
  let kk := (n' :: kk0 :: rest)[(n' :: kk0 :: rest).length - 1]
  let Xr0 : Tensor α [nn] :=
    cast (congrArg (Tensor α) rfl) (X.resize ⟨0, by grind⟩ nn)
  let Xr : Tensor α (bs' ++ [1, nn]) :=
    Xr0.reshape (bs' ++ [1, nn]) (by simp)
  have hs1 : (n' :: kk0 :: rest) = bs' ++ [nn1, kk] :=
    (List.EqAppendTake__ListGet.of.GeLength_2
      (s := n' :: kk0 :: rest) (by simp)).symm
  let d : Fin (bs' ++ [nn1, kk]).length := ⟨bs'.length, by grind⟩
  have hs2 :
      (bs' ++ [nn1, kk]).set d nn = bs' ++ [nn, kk] := by
    rw [List.SetAppend.eq.Append_Set.of.LeLength (Nat.le_refl _)
        [nn1, kk] nn]
    have hsub : (bs'.length - bs'.length) = 0 := by omega
    rw [hsub, List.Set_0.eq.Cons_Tail.of.GtLength_0 (by simp)]
    simp
  let Yt :=
    cast (congrArg (Tensor α) hs2)
      ((cast (congrArg (Tensor α) hs1)
        (0 : Tensor α (n' :: kk0 :: rest))).resize d nn)
  have hY : Yt = 0 :=
    castResizeCast0'0 d nn
      (congrArg (Tensor α) hs1) hs1
      (congrArg (Tensor α) hs2) hs2
  have hb : Xr.bmm Yt = 0 :=
    (congrArg (fun Y => Xr.bmm Y) hY).trans (bmm0'0 Xr)
  let or : Fin (bs' ++ [1, kk]).length :=
    ⟨(n' :: kk0 :: rest).length - 2, by
      simp [bs', List.length_append]; omega⟩
  let i : Fin ((bs' ++ [1, kk])[or]) := ⟨0, by
    have hlen : bs'.length = (n' :: kk0 :: rest).length - 2 := by
      simp [bs', List.length_take]; omega
    have hle : bs'.length ≤ (↑or : ℕ) := by
      rw [hlen]
    show 0 < (bs' ++ [1, kk])[(↑or : ℕ)]
    rw [List.getElem_append_right hle]
    simp [hlen, or]⟩
  have hp : (bs' ++ [1, kk]).eraseIdx ((n' :: kk0 :: rest).length - 2) =
      Tensor.matmul_shape [n] (n' :: kk0 :: rest) := by
    unfold Tensor.matmul_shape
    rw [dif_neg (by simp), dif_neg (by simp), dif_pos (by simp)]
    simp [bs', kk]
    rw [List.EraseIdxAppend.eq.Append_EraseIdx.of.LeLength (by grind)]
    simp only [List.EraseIdx.eq.Append_Drop_Add_1]
    have hmin : rest.length ⊓ (rest.length + 2) = rest.length := by
      rw [Nat.min_eq_left (by omega)]
    simp [hmin]
    exact (List.Drop.eq.ListGet.of.GtLength_0 (by simp)).symm
  have hz : cast (congrArg (Tensor α) hp) ((Xr.bmm Yt).select or i) = 0 :=
    (congrArg (fun Z => cast (congrArg (Tensor α) hp) (Z.select or i)) hb).trans
      ((congrArg (fun t => cast (congrArg (Tensor α) hp) t)
          (select0'0 or i)).trans
        (tcast0_heq (congrArg (Tensor α) hp) hp))
  convert hz
  · simp
  · simp (config := { zeta := true }) only [Xr0, Xr, bs']; rfl
  · simp

-- einsum with rank 1 on the left and zero on the right
private lemma dot1_0
  [NonUnitalNonAssocSemiring α]
  {n : ℕ} {s' : List ℕ}
  (X : Tensor α [n]) :
  X @ (0 : Tensor α s') = (0 : Tensor α (Tensor.matmul_shape [n] s')) := by
  show Tensor.einsum X (0 : Tensor α s') = _
  unfold Tensor.einsum
  cases s' with
  | nil =>
    rw [dif_neg (by simp), dif_pos (by simp)]
    exact (congrArg (fun t => cast _ t)
      (mul0'0_getElem (s' := []) (i := (0 : Fin 1)) X)).trans
      (tcast0_heq _ (by
        unfold Tensor.matmul_shape
        rw [dif_neg (by simp), dif_pos (by simp)]))
  | cons n' s₂ =>
    cases s₂ with
    | nil =>
      rw [dif_neg (by simp), dif_neg (by simp), dif_pos (by simp)]
      let nn := n ⊔ n'
      let Xr0 : Tensor α [nn] := X.resize ⟨0, by simp⟩ nn
      let Yr0 : Tensor α [nn] := (0 : Tensor α [n']).resize ⟨0, by simp⟩ nn
      have hm : Xr0 * Yr0 = 0 :=
        (congrArg (fun y : Tensor α [nn] => Xr0 * y)
          (resize0'0 (s := [n']) ⟨0, by simp⟩ nn)).trans
          (mulS0'0 Xr0)
      exact (congrArg (fun (p : Tensor α [nn]) => p.sum) hm).trans
        (EqSum0_0 [nn] 0)
    | cons kk0 rest =>
      exact dot1_cons_0 X n'

-- einsum with rank ≥ 2 on the left, rank 0 zero on the right
private lemma dotN0_0
  [NonUnitalNonAssocSemiring α]
  {s : List ℕ}
  (X : Tensor α s)
  (h2 : 2 ≤ s.length) :
  X @ (0 : Tensor α []) = (0 : Tensor α (Tensor.matmul_shape s [])) := by
  show Tensor.einsum X (0 : Tensor α []) = _
  unfold Tensor.einsum
  rw [dif_neg (by omega), dif_pos (by simp)]
  have hs : s = Tensor.matmul_shape s [] := by
    unfold Tensor.matmul_shape
    rw [dif_neg (by omega), dif_pos (by simp)]
  exact (congrArg (fun t => cast _ t)
    (mul0'0_getElem (s' := []) (i := (0 : Fin 1)) X)).trans
    (tcast0_heq _ hs)

-- einsum with rank ≥ 2 on the left, rank 1 zero on the right
private lemma dotN1_0
  [NonUnitalNonAssocSemiring α]
  {s : List ℕ} {n' : ℕ}
  (X : Tensor α s)
  (h2 : 2 ≤ s.length) :
  X @ (0 : Tensor α [n']) = (0 : Tensor α (Tensor.matmul_shape s [n'])) := by
  show Tensor.einsum X (0 : Tensor α [n']) = _
  unfold Tensor.einsum
  rw [dif_neg (by omega), dif_neg (by simp), dif_neg (by omega),
    dif_pos (by simp)]
  simp (config := { zeta := true }) only []
  let bs := s.take (s.length - 2)
  let k := s[s.length - 2]
  let nn := s[s.length - 1] ⊔ n'
  let X0 : Tensor α (bs ++ [k, s[s.length - 1]]) :=
    cast (by rwa [List.EqAppendTake__ListGet.of.GeLength_2]) X
  let Xr : Tensor α (bs ++ [k, nn]) :=
    cast (congrArg (Tensor α) (by simp))
      (X0.resize ⟨bs.length + 1, by grind⟩ nn)
  let Yt : Tensor α (bs ++ [nn, 1]) :=
    ((0 : Tensor α [n']).resize ⟨0, by grind⟩ nn).reshape
      (bs ++ [nn, 1]) (by simp)
  have hY : Yt = 0 :=
    resizeReshape0'0 (s₁ := [n']) (s₃ := bs ++ [nn, 1])
      ⟨0, by simp⟩ nn (by simp)
  have hb : Xr.bmm Yt = 0 :=
    (congrArg (fun Y => Xr.bmm Y) hY).trans (bmm0'0 Xr)
  let or : Fin (bs ++ [k, 1]).length :=
    ⟨s.length - 1, by simp [bs]; omega⟩
  let i : Fin ((bs ++ [k, 1])[or]) := ⟨0, by
    have hlen : bs.length = s.length - 2 := by
      simp [bs, List.length_take]
    have ho : (↑or : ℕ) = s.length - 1 := rfl
    have hle : bs.length ≤ (↑or : ℕ) := by omega
    have hidx : (↑or : ℕ) = bs.length + 1 := by omega
    have h : (bs ++ [k, 1])[or] = 1 := by
      show (bs ++ [k, 1])[(↑or : ℕ)] = 1
      simp [hidx, List.getElem_append_right]
    rw [h]; exact zero_lt_one⟩
  have hp : (bs ++ [k, 1]).eraseIdx (s.length - 1) =
      Tensor.matmul_shape s [n'] := by
    unfold Tensor.matmul_shape
    rw [dif_neg (by omega), dif_neg (by simp), dif_neg (by omega),
      dif_pos (by simp)]
    simp [bs, k]
    rw [List.EraseIdxAppend.eq.Append_EraseIdx.of.LeLength (by grind)]
    simp [List.EraseIdx.eq.Append_Drop_Add_1]
    simp [show s.length - 1 - (s.length - 2) = 1 by omega]
    simp [show s.length - 2 + 1 = s.length - 1 by omega]
    rw [List.DropLast.eq.Take_SubLength_1]
  have hz : cast (congrArg (Tensor α) hp) ((Xr.bmm Yt).select or i) = 0 :=
    (congrArg (fun Z => cast (congrArg (Tensor α) hp) (Z.select or i)) hb).trans
      ((congrArg (fun t => cast (congrArg (Tensor α) hp) t)
          (select0'0 or i)).trans
        (tcast0_heq (congrArg (Tensor α) hp) hp))
  convert hz
  · simp (config := { zeta := true }) only [Yt, bs]; rfl

-- einsum with rank ≥ 2 on both sides and zero on the right
private lemma dotNN_0
  [NonUnitalNonAssocSemiring α]
  {s s' : List ℕ}
  (X : Tensor α s)
  (h2 : 2 ≤ s.length)
  (h2' : 2 ≤ s'.length) :
  X @ (0 : Tensor α s') = (0 : Tensor α (Tensor.matmul_shape s s')) := by
  show Tensor.einsum X (0 : Tensor α s') = _
  unfold Tensor.einsum
  rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega),
    dif_neg (by omega)]
  simp (config := { zeta := true }) only []
  let bs := s.take (s.length - 2)
  let bs' := s'.take (s'.length - 2)
  let m := s[s.length - 2]
  let nn := s[s.length - 1]
  let n2 := s'[s'.length - 2]
  let kk := s'[s'.length - 1]
  have hs1 : s' = bs' ++ [n2, kk] := by
    rwa [List.EqAppendTake__ListGet.of.GeLength_2]
  let d : Fin (bs' ++ [n2, kk]).length := ⟨bs'.length, by grind⟩
  have hs2 :
      (bs' ++ [n2, kk]).set d (nn ⊔ n2) = bs' ++ [nn ⊔ n2, kk] := by
    rw [List.SetAppend.eq.Append_Set.of.LeLength (Nat.le_refl _)
        [n2, kk] (nn ⊔ n2)]
    have hsub : (bs'.length - bs'.length) = 0 := by omega
    rw [hsub, List.Set_0.eq.Cons_Tail.of.GtLength_0 (by simp)]
    simp
  let X0 : Tensor α (bs ++ [m, nn]) :=
    cast (by rwa [List.EqAppendTake__ListGet.of.GeLength_2]) X
  let Xr : Tensor α (bs ++ [m, nn ⊔ n2]) :=
    cast (congrArg (Tensor α) (by simp))
      (X0.resize ⟨bs.length + 1, by grind⟩ (nn ⊔ n2))
  let Yt : Tensor α (bs' ++ [nn ⊔ n2, kk]) :=
    cast (congrArg (Tensor α) hs2)
      ((cast (congrArg (Tensor α) hs1) (0 : Tensor α s')).resize
        d (nn ⊔ n2))
  have hY : Yt = 0 :=
    castResizeCast0'0 d (nn ⊔ n2)
      (congrArg (Tensor α) hs1) hs1
      (congrArg (Tensor α) hs2) hs2
  have htd : Xr.tensordot Yt = 0 :=
    (congrArg (fun Y => Xr.tensordot Y) hY).trans (tensordot0'0 Xr)
  exact (congrArg (fun Z => cast _ Z) htd).trans
    (tcast0_heq _ (by
      first
      | rfl
      | congr
        simp [Tensor.matmul_shape, Tensor.broadcast_shape]
        grind))


@[main]
private lemma main
  [NonUnitalNonAssocSemiring α]
-- given
  (X : Tensor α s) :
-- imply
  X @ (0 : Tensor α s') = 0 := by
-- proof
  cases s with
  | nil => exact dot0_0 X
  | cons n s₁ =>
    cases s₁ with
    | nil => exact dot1_0 X
    | cons _ _ =>
      cases s' with
      | nil => exact dotN0_0 X (by simp)
      | cons n' s₂ =>
        cases s₂ with
        | nil => exact dotN1_0 X (by simp)
        | cons _ _ => exact dotNN_0 X (by simp) (by simp)


-- created on 2026-09-10

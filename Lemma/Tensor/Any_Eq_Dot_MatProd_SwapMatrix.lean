import Lemma.Tensor.AppendHstackS.eq.MatProd_SwapMatrix.of.Le
import Lemma.Tensor.DotDot.eq.Dot_Dot
import Lemma.Tensor.DotGetSwapMatrix.eq.Get
import Lemma.Tensor.Dot_Hstack.eq.AppendDotS
import Lemma.Tensor.EqMul_0'0
import Lemma.Tensor.EqMul_1
open Tensor
set_option maxHeartbeats 4000000


private lemma mul_natCast_comm
  [Semiring α] [CharZero α]
  (x : Tensor α []) (n : ℕ) :
  x * (n : Tensor α []) = (n : Tensor α []) * x := by
  erw [Tensor.Mul, Tensor.Mul]
  apply Eq.of.EqDataS
  ext i
  simp only [Mul.mul]
  erw [Vector.GetMul.eq.MulGetS.fin, Vector.GetMul.eq.MulGetS.fin]
  have hn : (n : Tensor α []).data.get i = (n : α) := by
    change (⟨[n], by simp⟩ : Tensor α []).data.get i = (n : α)
    simp
    fin_cases i
    rfl
  rw [hn]
  exact (Nat.cast_commute n (x.data.get i)).symm.eq


private lemma swapMatrix_symmetric
  [Semiring α] [CharZero α]
  (n i₀ j₀ : ℕ) (i j : Fin n) :
  (SwapMatrix n i₀ j₀)[i][j] = (SwapMatrix (α := α) n i₀ j₀)[j][i] := by
  have hi := GetSwapMatrix.eq.Ite (α := α) i₀ j₀ i j
  have hj := GetSwapMatrix.eq.Ite (α := α) i₀ j₀ j i
  simp only [GetElem.getElem] at hi hj ⊢
  erw [hi, hj]
  simp only [Nat.Delta.eq.Ite]
  split_ifs <;> first | rfl | (simp at *; omega)


private lemma get_dot_swapMatrix_right
  [Semiring α] [CharZero α]
  (x : Tensor α [n]) (i j k : Fin n) :
  (x @ (SwapMatrix (α := α) n i j))[k] =x[Equiv.swap i j k] := by
  have hL := GetDot.eq.Sum_MulGetS.une x (SwapMatrix n i j) k
  have hR := GetDot.eq.Sum_MulGetS.mv (SwapMatrix n i j) x k
  have hLeft := DotGetSwapMatrix.eq.Get x i j k
  have hget := GetDot.eq.DotGet.une (SwapMatrix n i j) x k
  apply hL.trans
  apply Eq.trans _ (hget.trans hLeft)
  apply Eq.trans _ hR.symm
  apply Fin.Sum.of.All_Eq
  intro m
  have hsym := swapMatrix_symmetric (α := α) n i j m k
  refine (congrArg₂ (fun a b => id (α := Tensor α []) a * id (α := Tensor α []) b) (rfl : (x[m] : Tensor α []) = x[m]) hsym).trans ?_
  have hW := GetSwapMatrix.eq.Ite (α := α) (i) (j) k m
  simp only [id]
  simp only [GetElem.getElem] at hW ⊢
  erw [hW]
  split_ifs <;> exact mul_natCast_comm _ _


private lemma swapMatrix_eq_eye
  [Semiring α] [CharZero α]
  (n : ℕ) (i : Fin n) :
  SwapMatrix (α := α) n i i = eye n := by
  apply Tensor.Eq.of.All_EqGetS.fin
  intro a
  apply Tensor.Eq.of.All_EqGetS.fin
  intro b
  have hW := GetSwapMatrix.eq.Ite (α := α) (i) (i) a b
  have hI := (GetEye.eq.Delta.fin (α := α) a b).symm
  refine (hW.trans ?_).trans hI
  by_cases ha : (a : ℕ) = i
  ·
    simp [ha, Nat.Delta.eq.Ite]
    have : a = i := Fin.ext ha
    subst this
    simp [Fin.ext_iff, eq_comm]
    rfl
  ·
    simp [ha, Nat.Delta.eq.Ite, eq_comm]
    rfl


private lemma vector_dot_eye
  [Semiring α] [CharZero α]
  (x : Tensor α [n]) :
  x @ (eye (α := α) n) = x := by
  apply Tensor.Eq.of.All_EqGetS.fin
  intro j
  have h := GetDot.eq.Sum_MulGetS.une x (eye n) j
  apply h.trans
  apply (Finset.sum_eq_single j ?_ ?_).trans ?_
  ·
    intro k _ hk
    apply (congrArg (fun t : Tensor α [] => id (α := Tensor α []) (x[k] : Tensor α []) * id (α := Tensor α []) t) (GetEye.eq.Delta.fin k j)).trans
    simp [Nat.Delta.eq.Ite, hk]
    apply Tensor.EqMul_0'0.nat
  ·
    intro hj
    exact (hj (Finset.mem_univ _)).elim
  ·
    apply (congrArg (fun t : Tensor α [] => id (α := Tensor α []) (x[j] : Tensor α []) * id (α := Tensor α []) t) (GetEye.eq.Delta.fin j j)).trans
    simp [Nat.Delta.eq.Ite]
    apply Tensor.EqMul_1.nat


private lemma matProd_one_swap
  [Semiring α] [CharZero α]
  (b0 : ℕ) :
  matProd 1 (fun _ : Fin 1 => SwapMatrix 2 0 b0) = SwapMatrix (α := α) 2 0 b0 := by
  apply Eq.trans (MatProd.eq.DotMatProd (f := fun _ : Fin 1 => SwapMatrix 2 0 b0))
  simp only [matProd]
  exact EqDotEye (SwapMatrix 2 0 b0)


private lemma matProd_two
  [Semiring α] [CharZero α]
  (b0 b1 : ℕ) :
  matProd 2 (fun i : Fin 2 => SwapMatrix 2 i (if (i : ℕ) = 0 then b0 else b1)) = (SwapMatrix (α := α) 2 0 b0) @ (SwapMatrix (α := α) 2 1 b1) := by
  apply (MatProd.eq.DotMatProd (f := fun i : Fin 2 => SwapMatrix 2 i (if (i : ℕ) = 0 then b0 else b1))).trans
  have h1 : matProd 1 (fun i : Fin 1 => SwapMatrix 2 i.castSucc (if (i.castSucc : ℕ) = 0 then b0 else b1)) = SwapMatrix (α := α) 2 0 b0 := by
    have hfun : (fun i : Fin 1 => SwapMatrix 2 i.castSucc (if (i.castSucc : ℕ) = 0 then b0 else b1)) = fun _ : Fin 1 => SwapMatrix (α := α) 2 0 b0 := by
      funext i
      fin_cases i
      simp
    rw [hfun]
    exact matProd_one_swap b0
  rw [h1]
  rfl


private lemma matProd_id_eq_eye
  [Semiring α] [CharZero α] :
  matProd 2 (fun i : Fin 2 => SwapMatrix 2 i i) = eye (α := α) 2 := by
  have hfun : (fun i : Fin 2 => SwapMatrix 2 i i) = fun i : Fin 2 => SwapMatrix (α := α) 2 i (if (i : ℕ) = 0 then 0 else 1) := by
    funext i
    fin_cases i <;> simp
  rw [congrArg (fun f => matProd 2 f) hfun, matProd_two 0 1]
  have e0 : SwapMatrix (α := α) 2 0 0 = eye 2 := by
    simpa using swapMatrix_eq_eye (α := α) 2 (0 : Fin 2)
  have e1 : SwapMatrix (α := α) 2 1 1 = eye 2 := by
    simpa using swapMatrix_eq_eye 2 (1 : Fin 2)
  rw [e0, e1]
  exact EqDotEye (eye 2)


private lemma matProd_const0_eq_swap
  [Semiring α] [CharZero α] :
  matProd 2 (fun i : Fin 2 => SwapMatrix 2 i (0 : Fin 2)) = SwapMatrix (α := α) 2 1 0 := by
  have hfun : (fun i : Fin 2 => SwapMatrix 2 i (0 : Fin 2)) = fun i : Fin 2 => SwapMatrix (α := α) 2 i (if (i : ℕ) = 0 then 0 else 0) := by
    funext i
    simp
  rw [congrArg (fun f => matProd 2 f) hfun, matProd_two 0 0]
  have e0 : SwapMatrix (α := α) 2 0 0 = eye 2 := by
    simpa using swapMatrix_eq_eye 2 (0 : Fin 2)
  rw [e0]
  exact EqDotEye (SwapMatrix 2 1 0)


private lemma natCast_tensor_inj
  [Semiring α] [CharZero α]
  {m k : ℕ}
  (h : (m : Tensor α []) = (k : Tensor α [])) :
  m = k := by
  have hd := congrArg (fun t : Tensor α [] => t.data.get ⟨0, by simp⟩) h
  have hm : (m : Tensor α []).data.get ⟨0, by simp⟩ = (m : α) := by
    simp
    rfl
  have hk : (k : Tensor α []).data.get ⟨0, by simp⟩ = (k : α) := by
    simp
    rfl
  rw [hm, hk] at hd
  exact CharZero.cast_injective hd


private lemma vector_dot_zero
  [Semiring α] [CharZero α]
  (x : Tensor α [n]) {m : ℕ} :
  x @ (0 : Tensor α [n, m]) = (0 : Tensor α [m]) := by
  apply (Dot.eq.GetDotUnsqueeze_0 x _).trans
  apply (Get.of.Eq.fin (EqDot_0'0 (x.unsqueeze 0)) _).trans
  apply EqGet0_0.fin


private lemma vector_dot_rowAppend
  [Semiring α] [CharZero α]
  (x : Tensor α [n]) (y : Tensor α [m])
  (P : Tensor α [n, k]) (Q : Tensor α [m, k]) :
  (x ++ y) @ (P ++ Q) = id (α := Tensor α [k]) (x @ P) + id (α := Tensor α [k]) (y @ Q) := by
  apply Tensor.Eq.of.All_EqGetS.fin
  intro j
  trans (id (α := Tensor α [k]) (x @ P))[j] + (id (α := Tensor α [k]) (y @ Q))[j]
  .
    apply (GetDot.eq.Sum_MulGetS.une _ _ j).trans
    rw [Fin.sum_univ_add]
    have h1 : (∑ i : Fin n, (x ++ y)[Fin.castAdd m i] * id (α := Tensor α []) (P ++ Q)[Fin.castAdd m i][j]) = ∑ i : Fin n, x[i] * id (α := Tensor α []) P[i][j] := by
      apply Fin.Sum.of.All_Eq
      intro i
      apply congrArg₂ (fun (a b : Tensor α []) => id (α := Tensor α []) a * b)
      ·
        simpa [GetElem.getElem, Fin.castAdd] using GetAppend.eq.Get.of.Lt (A := x) (B := y) i.isLt
      ·
        apply congrArg (fun t : Tensor α [k] => (t[j] : Tensor α []))
        simpa [GetElem.getElem, Fin.castAdd] using GetAppend.eq.Get.of.Lt (A := P) (B := Q) i.isLt
    have h2 : (∑ i : Fin m, (x ++ y)[Fin.natAdd n i] * id (α := Tensor α []) (P ++ Q)[Fin.natAdd n i][j]) = ∑ i : Fin m, y[i] * id (α := Tensor α []) Q[i][j] := by
      apply Fin.Sum.of.All_Eq
      intro i
      apply congrArg₂ (fun (a b : Tensor α []) => id (α := Tensor α []) a * b)
      ·
        simpa [GetElem.getElem, Fin.natAdd, Nat.add_sub_cancel_left] using GetAppend.eq.Get_Sub.of.GtAdd.Ge (A := x) (B := y) (Nat.le_add_right n (i : ℕ)) (Nat.add_lt_add_left i.isLt n)
      ·
        apply congrArg (fun t : Tensor α [k] => (t[j] : Tensor α []))
        simpa [GetElem.getElem, Fin.natAdd, Nat.add_sub_cancel_left] using GetAppend.eq.Get_Sub.of.GtAdd.Ge (A := P) (B := Q) (Nat.le_add_right n (i : ℕ)) (Nat.add_lt_add_left i.isLt n)
    erw [h1, h2, ← GetDot.eq.Sum_MulGetS.une x P j, ← GetDot.eq.Sum_MulGetS.une y Q j]
    rfl
  .
    symm
    apply GetAdd.eq.AddGetS.fin


private lemma idStack_dot_embed
  [Semiring α] [CharZero α]
  (M : Tensor α [n, n]) :
  (([i < n + 1] ((i : ℕ) : Tensor α [])) @ (M.hstack (0 : Tensor α [n, 1]) ++ (0 : Tensor α [1, n]).hstack (eye 1))) = id (α := Tensor α [n]) (([i < n] ((i : ℕ) : Tensor α [])) @ M) ++ [_ < 1] (n : Tensor α []) := by
  have htail : [i < 1] (↑(n + i) : Tensor α []) = [_ < 1] (n : Tensor α []) := by
    apply Tensor.Eq.of.All_EqGetS.fin
    intro i
    fin_cases i
    simp [EqGetStack.fin]
  rw [Stack.eq.AppendStackS (n := n) (j := 1) (fun i => (i : Tensor α [])), htail]
  let x := [i < n] ((i : ℕ) : Tensor α [])
  let y := [i < 1] (n : Tensor α [])
  let P := M.hstack (0 : Tensor α [n, 1])
  let Q := (0 : Tensor α [1, n]).hstack (eye 1)
  apply (vector_dot_rowAppend x y P Q).trans
  rw [Dot_Hstack.eq.AppendDotS, vector_dot_zero x, Dot_Hstack.eq.AppendDotS, vector_dot_zero y, vector_dot_eye y]
  apply (AddAppendS.eq.AppendAddS _ _ _ _).trans
  grind


private lemma dot_swapMatrix_involutive
  [Semiring α] [CharZero α]
  (x : Tensor α [n]) (i j : Fin n) :
  ((x @ (SwapMatrix (α := α) n i j)) @ (SwapMatrix (α := α) n i j)) = x := by
  apply Tensor.Eq.of.All_EqGetS.fin
  intro k
  have h1 := get_dot_swapMatrix_right (α := α) (x @ (SwapMatrix (α := α) n i j)) i j k
  have h0 := get_dot_swapMatrix_right (α := α) x i j (Equiv.swap i j k)
  apply h1.trans
  apply Eq.trans h0
  rw [Equiv.swap_apply_self]
  rfl


private lemma base_two
  [Semiring α] [CharZero α]
  (p : Tensor α [2])
  (hp : Set.range (fun i : Fin 2 => p[i]) = Set.range (fun i : Fin 2 => ((i : ℕ) : Tensor α []))) :
  ∃ b : Fin 2 → Fin 2, p = ([i < 2] ((i : ℕ) : Tensor α [])) @ matProd 2 (fun i => SwapMatrix (α := α) 2 i (b i)) := by
  have hR : Set.range (fun i : Fin 2 => ((i : ℕ) : Tensor α [])) = {((0 : ℕ) : Tensor α []), ((1 : ℕ) : Tensor α [])} := by
    ext x
    constructor
    ·
      intro hx
      obtain ⟨i, hi⟩ := hx
      fin_cases i <;> aesop
    ·
      intro hx
      simp at hx
      obtain h | h := hx <;> aesop
  have hp' := hp.trans hR
  have mem_pair (j : Fin 2) : (p[j] : Tensor α []) = ((0 : ℕ) : Tensor α []) ∨ (p[j] : Tensor α []) = ((1 : ℕ) : Tensor α []) := by
    apply (Set.mem_insert_iff.mp _).elim Or.inl fun h => Or.inr (Set.mem_singleton_iff.mp h)
    erw [← hp']
    exact ⟨j, rfl⟩
  have h01 : ((0 : ℕ) : Tensor α []) ≠ ((1 : ℕ) : Tensor α []) := fun h => Nat.zero_ne_one (natCast_tensor_inj h)
  if h0 : (p[(0 : Fin 2)] : Tensor α []) = ((0 : ℕ) : Tensor α []) then
    refine ⟨fun i => i, ?_⟩
    rw [matProd_id_eq_eye (α := α), vector_dot_eye]
    apply Tensor.Eq.of.All_EqGetS.fin
    intro i
    fin_cases i
    ·
      exact h0.trans (EqGetStack.fin (fun i : Fin 2 => ((i : ℕ) : Tensor α [])) (0 : Fin 2)).symm
    ·
      obtain h1 | h1 := mem_pair (1 : Fin 2)
      ·
        apply (h01 (Set.mem_singleton_iff.1 _).symm).elim
        have hr : Set.range (fun i : Fin 2 => (p[i] : Tensor α [])) = {((0 : ℕ) : Tensor α [])} := by
          ext x
          constructor
          ·
            intro hx
            obtain ⟨j, hj⟩ := hx
            fin_cases j <;> grind
          ·
            intro hx
            exact ⟨(0 : Fin 2), h0.trans (Set.mem_singleton_iff.1 hx).symm⟩
        apply (hr.symm.trans hp').symm ▸ Set.mem_insert_of_mem _ (Set.mem_singleton _)
      ·
        exact h1.trans (EqGetStack.fin (fun i : Fin 2 => ((i : ℕ) : Tensor α [])) (1 : Fin 2)).symm
  else
    have h0' : (p[(0 : Fin 2)] : Tensor α []) = ((1 : ℕ) : Tensor α []) := by
      obtain (h | h) := mem_pair (0 : Fin 2) <;> aesop
    refine ⟨fun _ => (0 : Fin 2), ?_⟩
    rw [matProd_const0_eq_swap (α := α)]
    apply Tensor.Eq.of.All_EqGetS.fin
    intro k
    apply Eq.trans _ (get_dot_swapMatrix_right _ (1 : Fin 2) (0 : Fin 2) k).symm
    apply Eq.trans _ (EqGetStack.fin _ _).symm
    fin_cases k
    ·
      change (p[(0 : Fin 2)] : Tensor α []) = ((1 : ℕ) : Tensor α [])
      simpa [Equiv.swap_apply_def] using h0'
    ·
      obtain (h1 | h1) := mem_pair (1 : Fin 2)
      ·
        change (p[(1 : Fin 2)] : Tensor α []) = ((0 : ℕ) : Tensor α [])
        simpa [Equiv.swap_apply_def] using h1
      ·
        have hr' : Set.range (fun i : Fin 2 => (p[i] : Tensor α [])) = {((1 : ℕ) : Tensor α [])} := by
          ext x
          constructor
          ·
            intro hx
            obtain ⟨j, hj⟩ := hx
            fin_cases j <;> grind
          ·
            intro hx
            exact ⟨(0 : Fin 2), h0'.trans (Set.mem_singleton_iff.1 hx).symm⟩
        apply (h01 (Set.mem_singleton_iff.1 _)).elim
        apply (hr'.symm.trans hp').symm ▸ Set.mem_insert _ _


@[main]
private lemma main
  [Semiring α] [CharZero α]
  {n : ℕ}
  {P : Set (Tensor α [n])}
-- given
  (hn : n ≥ 2)
  (hP : P = {p | Set.range (fun i : Fin n => p[i]) = Set.range (fun i : Fin n => ((i : ℕ) : Tensor α []))}) :
-- imply
  ∀ p ∈ P, ∃ b : Fin n → Fin n, p = ([i < n] ((i : ℕ) : Tensor α [])) @ matProd n (fun i => SwapMatrix (α := α) n i (b i)) := by
-- proof
  rw [hP]
  intro p hp
  simp only [Set.mem_ofPred_eq] at hp
  have H : ∀ m, m ≥ 2 → ∀ (p : Tensor α [m]),
    Set.range (fun i : Fin m => (p[i] : Tensor α [])) = Set.range (fun i : Fin m => ((i : ℕ) : Tensor α [])) →
      ∃ b : Fin m → Fin m, p = ([i < m] ((i : ℕ) : Tensor α [])) @ matProd m (fun i => SwapMatrix (α := α) m i (b i)) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base =>
      intro p hp
      exact base_two p hp
    | succ n hn ih =>
      intro p hp
      have hex : ∃ j : Fin (n + 1), (p[j] : Tensor α []) = (n : Tensor α []) := by
        have hmem' : (n : Tensor α []) ∈ Set.range (fun i : Fin (n + 1) => (p[i] : Tensor α [])) := by
          rw [hp]
          exact ⟨Fin.last n, by simp [Fin.val_last]⟩
        apply hmem'
      obtain ⟨j, hj⟩ := hex
      let W := SwapMatrix (α := α) (n + 1) (Fin.last n) j
      let p' : Tensor α [n + 1] := id (α := Tensor α [n + 1]) (p @ W)
      have hp't : ∀ t : Fin (n + 1), (p'[t] : Tensor α []) = (p[Equiv.swap (Fin.last n) j t] : Tensor α []) := by
        intro t
        exact get_dot_swapMatrix_right p (Fin.last n) j t
      have hplast : (p'[Fin.last n] : Tensor α []) = (n : Tensor α []) := by
        rw [hp't, Equiv.swap_apply_left, hj]
      have hp' : Set.range (fun i : Fin (n + 1) => (p'[i] : Tensor α [])) = Set.range (fun i : Fin (n + 1) => ((i : ℕ) : Tensor α [])) := by
        apply Eq.trans _ hp
        ext x
        constructor
        ·
          intro hx
          obtain ⟨t, ht⟩ := hx
          refine ⟨Equiv.swap (Fin.last n) j t, ?_⟩
          exact ((hp't t).symm.trans ht)
        ·
          intro hx
          obtain ⟨t, ht⟩ := hx
          refine ⟨Equiv.swap (Fin.last n) j t, ?_⟩
          calc
            _ = (p[Equiv.swap (Fin.last n) j (Equiv.swap (Fin.last n) j t)] : Tensor α []) := hp't _
            _ = (p[t] : Tensor α []) := by
              rw [Equiv.swap_apply_self]
            _ = x := ht
      let q : Tensor α [n] := [i < n] (p'[i.castSucc] : Tensor α [])
      have hq_get : ∀ i : Fin n, (q[i] : Tensor α []) = (p'[i.castSucc] : Tensor α []) := by
        intro i
        simp only [q, GetElem.getElem]
        exact EqGetStack.fin (fun i : Fin n => (p'[i.castSucc] : Tensor α [])) i
      have hp_inj : Function.Injective fun i : Fin (n + 1) => (p[i] : Tensor α []) := by
        intro a b hab
        let σ : Fin (n + 1) → Fin (n + 1) := fun i =>
          have : ∃ j : Fin (n + 1), ((j : ℕ) : Tensor α []) = (p[i] : Tensor α []) := by
            have : (p[i] : Tensor α []) ∈ Set.range (fun j : Fin (n + 1) => ((j : ℕ) : Tensor α [])) := by
              rw [← hp]
              exact ⟨i, rfl⟩
            simpa [Set.mem_range]
          Classical.choose this
        have hσ : ∀ i, ((σ i : ℕ) : Tensor α []) = (p[i] : Tensor α []) := fun i =>
          have : ∃ j : Fin (n + 1), ((j : ℕ) : Tensor α []) = (p[i] : Tensor α []) := by
            have : (p[i] : Tensor α []) ∈ Set.range (fun j : Fin (n + 1) => ((j : ℕ) : Tensor α [])) := by
              rw [← hp]
              exact ⟨i, rfl⟩
            simpa [Set.mem_range]
          Classical.choose_spec this
        apply (Finite.injective_iff_surjective (f := σ)).2 _ (Fin.ext (natCast_tensor_inj ((hσ a).trans (hab.trans (hσ b).symm))))
        intro k
        have : ((k : ℕ) : Tensor α []) ∈
            Set.range (fun i : Fin (n + 1) => (p[i] : Tensor α [])) := by
          rw [hp]
          exact ⟨k, rfl⟩
        obtain ⟨i, hi⟩ := this
        refine ⟨i, ?_⟩
        exact Fin.ext (natCast_tensor_inj ((hσ i).trans hi))
      have hq : Set.range (fun i : Fin n => (q[i] : Tensor α [])) = Set.range (fun i : Fin n => ((i : ℕ) : Tensor α [])) := by
        ext x
        constructor
        ·
          intro hx
          obtain ⟨i, rfl⟩ := hx
          have hmem : (q[i] : Tensor α []) ∈ Set.range (fun t : Fin (n + 1) => ((t : ℕ) : Tensor α [])) := by
            rw [← hp']
            exact ⟨i.castSucc, (hq_get i).symm⟩
          obtain ⟨t, ht⟩ := hmem
          have ht_ne : t ≠ Fin.last n := by
            intro ht_eq
            have hp'_inj : Function.Injective fun i : Fin (n + 1) => (p'[i] : Tensor α []) := by
              intro a b hab
              apply (Equiv.swap (Fin.last n) j).injective
              apply hp_inj
              exact ((hp't a).symm.trans hab).trans (hp't b)
            have hunique : ∀ t : Fin (n + 1), (p'[t] : Tensor α []) = (n : Tensor α []) → t = Fin.last n := by
              intro t ht
              exact hp'_inj (ht.trans hplast.symm)
            apply (Fin.castSucc_lt_last i).ne (hunique _ _)
            apply (hq_get i).symm.trans
            apply ht.symm.trans
            rw [ht_eq]
            simp [Fin.val_last]
          obtain ⟨t0, rfl⟩ := Fin.eq_castSucc_of_ne_last ht_ne
          refine ⟨t0, ?_⟩
          apply (show ((t0 : ℕ) : Tensor α []) = (((t0.castSucc) : ℕ) : Tensor α []) by simp [Fin.val_castSucc]).trans ht
        ·
          intro hx
          obtain ⟨i, rfl⟩ := hx
          have hmem : ((i : ℕ) : Tensor α []) ∈ Set.range (fun t : Fin (n + 1) => (p'[t] : Tensor α [])) := by
            rw [hp']
            exact ⟨i.castSucc, by simp⟩
          obtain ⟨t, ht⟩ := hmem
          have ht_ne : t ≠ Fin.last n := by
            intro ht_eq
            apply (Nat.ne_of_lt i.isLt)
            apply natCast_tensor_inj (α := α)
            apply ht.symm.trans
            apply (by rw [ht_eq] : (p'[t] : Tensor α []) = (p'[Fin.last n] : Tensor α [])).trans hplast
          obtain ⟨t0, rfl⟩ := Fin.eq_castSucc_of_ne_last ht_ne
          refine ⟨t0, ?_⟩
          exact (hq_get t0).trans ht
      obtain ⟨b0, hb0⟩ := ih q hq
      let M := matProd n (fun i => SwapMatrix (α := α) n i (b0 i))
      have hp'_factor : p' = (([i < n + 1] ((i : ℕ) : Tensor α [])) @ matProd n (fun i => SwapMatrix (n + 1) i (b0 i))) := calc
        _ = q ++ [i < 1] (n : Tensor α []) := by
          apply Eq.of.All_EqGetS.fin
          intro t
          refine Fin.lastCases ?_ ?_ t
          ·
            apply hplast.trans (((EqGetStack.fin (fun _ : Fin 1 => (n : Tensor α [])) (0 : Fin 1)).symm).trans ?_)
            erw [GetAppend.eq.Get_Sub.of.GtAdd.Ge.fin (by simp) (by simp)]
            simp
            rfl
          ·
            intro i
            apply (hq_get i).symm.trans
            symm
            simp [GetElem.getElem]
            apply GetAppend.eq.Get.of.Lt.fin
        _ = id (α := Tensor α [n]) (([i < n] ((i : ℕ) : Tensor α [])) @ M) ++ [i < 1] (n : Tensor α []) := by congr 1
        _ = id (α := Tensor α [n + 1]) (([i < n + 1] ((i : ℕ) : Tensor α [])) @ (M.hstack (0 : Tensor α [n, 1]) ++ (0 : Tensor α [1, n]).hstack (eye 1))) := (idStack_dot_embed _).symm
        _ = id (α := Tensor α [n + 1]) (([i < n + 1] ((i : ℕ) : Tensor α [])) @ matProd n (fun i => SwapMatrix (α := α) (n + 1) i (b0 i))) := by
          rw [AppendHstackS.eq.MatProd_SwapMatrix.of.Le le_rfl]
      have hp_recover : p = p' @ W := by
        simp only [p']
        symm
        exact dot_swapMatrix_involutive p (Fin.last n) j
      let b : Fin (n + 1) → Fin (n + 1) := Fin.append (fun i : Fin n => (b0 i).castSucc) (fun _ : Fin 1 => j)
      refine ⟨b, ?_⟩
      apply (((hp_recover.trans (congrArg (fun t : Tensor α [n + 1] => id (α := Tensor α [n + 1]) (t @ W)) hp'_factor)).trans (DotDot.eq.Dot_Dot.vmm _ _ _)).trans _).trans rfl
      apply congrArg
      symm
      apply MatProd.eq.DotMatProd.trans
      have hb_last : b (Fin.last n) = j := by
        change Fin.append (fun i : Fin n => (b0 i).castSucc) (fun _ : Fin 1 => j) (Fin.natAdd n (0 : Fin 1)) = j
        rw [Fin.append_right]
      simp only [hb_last]
      have hb_cast : ∀ i : Fin n, b i.castSucc = (b0 i).castSucc := by
        intro i
        change Fin.append (fun i : Fin n => (b0 i).castSucc) (fun _ : Fin 1 => j) (Fin.castAdd 1 i) = (b0 i).castSucc
        rw [Fin.append_left]
      conv_lhs =>
        lhs
        arg 2
        ext i
        simp [hb_cast i]
  aesop


-- created on 2020-09-01
-- updated on 2026-09-09

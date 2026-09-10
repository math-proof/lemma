import Lemma.Set.In_Range.is.Any_Eq
import Lemma.Tensor.AppendHstackS.eq.MatProd_SwapMatrix.of.Le
import Lemma.Tensor.Coe.is.Eq
import Lemma.Tensor.DotAppendHstackS.eq.AppendDotS
import Lemma.Tensor.DotDot.eq.Dot_Dot
import Lemma.Tensor.EqDotDot_SwapMatrix
import Lemma.Tensor.EqDot_Eye
import Lemma.Tensor.EqMatProd
import Lemma.Tensor.MatProd.eq.Dot
import Lemma.Tensor.MatProd.eq.Eye
open Tensor
set_option maxHeartbeats 4000000


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
      have h01 : ((0 : ℕ) : Tensor α []) ≠ ((1 : ℕ) : Tensor α []) := fun h => Nat.zero_ne_one (Eq.of.Coe h)
      if h0 : (p[(0 : Fin 2)] : Tensor α []) = ((0 : ℕ) : Tensor α []) then
        refine ⟨fun i => i, ?_⟩
        rw [MatProd.eq.Eye, EqDot_Eye.vm]
        apply Eq.of.All_EqGetS.fin
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
        conv_rhs =>
          arg 2
          rw [show (fun i : Fin 2 => SwapMatrix 2 i (0 : Fin 2)) = fun i : Fin 2 => SwapMatrix (α := α) 2 i (if (i : ℕ) = 0 then 0 else 0) by funext i; simp]
          simp only [MatProd.eq.Dot, SwapMatrix.eq.Eye]
          exact EqDotEye (SwapMatrix 2 1 0)
        apply Eq.of.All_EqGetS.fin
        intro k
        apply Eq.trans _ (GetDot_SwapMatrix.eq.Get _ (1 : Fin 2) (0 : Fin 2) k).symm
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
            have hr' : {((1 : ℕ) : Tensor α [])} = Set.range (fun i : Fin 2 => (p[i] : Tensor α [])) := by
              ext x
              constructor
              ·
                intro hx
                exact ⟨(0 : Fin 2), h0'.trans (Set.mem_singleton_iff.1 hx).symm⟩
              ·
                intro hx
                obtain ⟨j, hj⟩ := hx
                fin_cases j <;> grind
            apply (h01 (Set.mem_singleton_iff.1 _)).elim
            apply (hr'.trans hp').symm ▸ Set.mem_insert _ _
    | succ n hn ih =>
      intro p hp
      obtain ⟨j, hj⟩ := Set.Any_Eq.of.In_Range (hp.symm ▸ Set.In_Range.of.Any_Eq (a := (n : Tensor α [])) ⟨Fin.last n, by simp [Fin.val_last]⟩)
      let W := SwapMatrix (α := α) (n + 1) (Fin.last n) j
      let p' : Tensor α [n + 1] := id (α := Tensor α [n + 1]) (p @ W)
      have hp't : ∀ t : Fin (n + 1), (p'[t] : Tensor α []) = (p[Equiv.swap (Fin.last n) j t] : Tensor α []) := by
        intro t
        exact GetDot_SwapMatrix.eq.Get p (Fin.last n) j t
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
        apply (Finite.injective_iff_surjective (f := σ)).2 _ (Fin.ext (Eq.of.Coe ((hσ a).trans (hab.trans (hσ b).symm))))
        intro k
        have : ((k : ℕ) : Tensor α []) ∈
            Set.range (fun i : Fin (n + 1) => (p[i] : Tensor α [])) := by
          rw [hp]
          exact ⟨k, rfl⟩
        obtain ⟨i, hi⟩ := this
        refine ⟨i, ?_⟩
        exact Fin.ext (Eq.of.Coe ((hσ i).trans hi))
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
            have h_eq : ((i : ℕ) : Tensor α []) = (n : Tensor α []) := ht.symm.trans ((by rw [ht_eq] : (p'[t] : Tensor α []) = (p'[Fin.last n] : Tensor α [])).trans hplast)
            exact Eq.of.Coe h_eq
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
        _ = id (α := Tensor α [n + 1]) (([i < n + 1] ((i : ℕ) : Tensor α [])) @ (M.hstack (0 : Tensor α [n, 1]) ++ (0 : Tensor α [1, n]).hstack (eye 1))) := (DotAppendHstackS.eq.AppendDotS (fun i => ((i : ℕ) : Tensor α [])) M).symm
        _ = id (α := Tensor α [n + 1]) (([i < n + 1] ((i : ℕ) : Tensor α [])) @ matProd n (fun i => SwapMatrix (α := α) (n + 1) i (b0 i))) := by
          rw [AppendHstackS.eq.MatProd_SwapMatrix.of.Le le_rfl]
      have hp_recover : p = p' @ W := by
        simp only [p']
        symm
        exact EqDotDot_SwapMatrix p (Fin.last n) j
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
-- updated on 2026-09-10

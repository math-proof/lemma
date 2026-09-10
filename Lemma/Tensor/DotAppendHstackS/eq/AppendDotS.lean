import Lemma.Tensor.AddAppendS.eq.AppendAddS
import Lemma.Tensor.DotAppendS.eq.AddDotS
import Lemma.Tensor.Dot_Hstack.eq.AppendDotS
import Lemma.Tensor.EqDot_0'0
import Lemma.Tensor.EqDot_Eye
open Tensor


@[main]
private lemma main
  [Semiring α] [CharZero α]
-- given
  (f : Fin (n + 1) → Tensor α [])
  (M : Tensor α [n, n]) :
-- imply
  ([i < n + 1] (f i)) @ (M.hstack (0 : Tensor α [n, 1]) ++ (0 : Tensor α [1, n]).hstack (eye 1)) =
    id (α := Tensor α [n]) (([i < n] (f (i.castAdd 1))) @ M) ++ [_ < 1] (f (Fin.last n)) := by
-- proof
  let g : ℕ → Tensor α [] := fun i => if h : i < n + 1 then f ⟨i, h⟩ else (0 : Tensor α [])
  have hg1 : ∀ (i : Fin (n + 1)), g (i : ℕ) = f i := by
    intro i
    have h : (i : ℕ) < n + 1 := i.isLt
    have hg : g (i : ℕ) = f ⟨(i : ℕ), h⟩ := by
      dsimp only [g]
      exact dif_pos h
    rw [hg]
  have hg2 : ∀ (i : Fin n), g (i : ℕ) = f (i.castAdd 1) := by
    intro i
    have h : (i : ℕ) < n + 1 := by omega
    have hg : g (i : ℕ) = f ⟨(i : ℕ), h⟩ := by
      dsimp only [g]
      exact dif_pos h
    rw [hg]
    apply congrArg f
    apply Fin.ext
    simp
  have hg3 : ∀ (i : Fin 1), g (n + (i : ℕ)) = f (Fin.last n) := by
    intro i
    have hz : n + (i : ℕ) = n := by
      fin_cases i
      omega
    rw [hz]
    have h : n < n + 1 := by omega
    have hg : g n = f ⟨n, h⟩ := by
      dsimp only [g]
      exact dif_pos h
    rw [hg]
    apply congrArg f
    apply Fin.ext
    simp [Fin.val_last]
  have h1 : [i < n + 1] (f i) = [i < n + 1] (g i) := by
    apply Eq.of.All_EqGetS.fin
    intro i
    simp [EqGetStack.fin, hg1 i]
  have h2 := Stack.eq.AppendStackS (n := n) (j := 1) g
  have h3 : [i < n] (g i) = [i < n] (f (i.castAdd 1)) := by
    apply Eq.of.All_EqGetS.fin
    intro i
    simp [EqGetStack.fin, hg2 i]
  have h4 : [i < 1] (g (n + i)) = [_ < 1] (f (Fin.last n)) := by
    apply Eq.of.All_EqGetS.fin
    intro i
    fin_cases i
    simpa [EqGetStack.fin, EqGetStack.fun] using hg3 0
  have hsplit : [i < n + 1] (f i) = [i < n] (f (i.castAdd 1)) ++ [_ < 1] (f (Fin.last n)) := by
    rw [h1, h2, h3, h4]
  rw [hsplit]
  let x := [i < n] (f (i.castAdd 1))
  let y := [_ < 1] (f (Fin.last n))
  let P := M.hstack (0 : Tensor α [n, 1])
  let Q := (0 : Tensor α [1, n]).hstack (eye 1)
  apply (DotAppendS.eq.AddDotS.vm x y P Q).trans
  have hx0 : x @ (0 : Tensor α [n, 1]) = (0 : Tensor α [1]) := EqDot_0'0 x
  have hy0 : y @ (0 : Tensor α [1, n]) = (0 : Tensor α [n]) := EqDot_0'0 y
  rw [Dot_Hstack.eq.AppendDotS, hx0, Dot_Hstack.eq.AppendDotS, hy0, EqDot_Eye.vm y]
  apply (AddAppendS.eq.AppendAddS _ _ _ _).trans
  simp only [id_eq, add_zero, zero_add]
  rfl


-- created on 2026-09-10

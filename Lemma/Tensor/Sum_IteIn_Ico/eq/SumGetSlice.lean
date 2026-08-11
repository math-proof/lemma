import Lemma.Fin.In_Ico.is.In_Ico_Min
import Lemma.List.LengthSlice.eq.SubMin
import Lemma.Tensor.GetGetSlice.eq.Get_Add.of.GtSubMin
import Lemma.Tensor.Sum_0.eq.Sum_Get
open Tensor List


@[main, fin]
private lemma main
  [AddCommMonoid α]
-- given
  (X : Tensor α (n :: s))
  (a b : ℕ) :
-- imply
  ∑ k : Fin n, (if ↑k ∈ Ico a b then
    X[k]
  else
    0) = X[a:b].sum 0 := by
-- proof
  rw [Sum_0.eq.Sum_Get]
  conv_rhs =>
    arg 2
    ext i
    erw [GetGetSlice.eq.Get_Add.of.GtSubMin (by
      have := i.isLt
      simp [Tensor.length, LengthSlice.eq.SubMin] at this ⊢
      exact this) X]
  conv_lhs =>
    arg 2
    ext k
    simp only [Fin.In_Ico.is.In_Ico_Min k a b]
  rw [← Finset.sum_filter]
  apply Eq.symm
  have h_len := LengthSlice.eq.SubMin b n a
  refine Finset.sum_bij (fun (i : Fin ((⟨a, b, 1⟩ : Slice).length X.length)) _ => (⟨a + ↑i, by grind [Tensor.length]⟩ : Fin n)) (by grind [Tensor.length]) (by grind) ?_ (by aesop)
  intro k hk
  refine ⟨⟨k.val - a, ?_⟩, Finset.mem_univ _, ?_⟩ <;> grind [Tensor.length]


-- created on 2026-08-11

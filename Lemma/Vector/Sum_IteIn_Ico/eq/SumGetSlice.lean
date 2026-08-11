import Lemma.Fin.In_Ico.is.In_Ico_Min
import Lemma.Vector.GetGetSlice.eq.Get_Add.of.GtSubMin
import Lemma.Vector.Sum.eq.Sum_Get
open Vector


@[main, fin]
private lemma main
  [AddCommMonoid α]
-- given
  (v : List.Vector α n)
  (a b : ℕ) :
-- imply
  ∑ k : Fin n, (if ↑k ∈ Ico a b then
    v[k]
  else
    0) = v[a:b].sum := by
-- proof
  rw [Sum.eq.Sum_Get.fin]
  conv_rhs =>
    arg 2
    ext i
    rw [Vector.GetGetSlice.eq.Get_Add.of.GtSubMin.fin (by simpa [List.LengthSlice.eq.SubMin] using i.isLt)]
  conv_lhs =>
    arg 2
    ext k
    simp [Fin.In_Ico.is.In_Ico_Min k a b]
  rw [← Finset.sum_filter]
  apply Eq.symm
  have h_len := List.LengthSlice.eq.SubMin b n a
  refine Finset.sum_bij (fun (i : Fin ((⟨a, b, 1⟩ : Slice).length n)) _ => (⟨a + ↑i, by grind⟩ : Fin n)) (by grind) (by grind) ?_ (by aesop)
  intro k hk
  refine ⟨⟨k.val - a, ?_⟩, Finset.mem_univ _, ?_⟩ <;> grind


-- created on 2026-08-08

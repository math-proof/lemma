import Lemma.Set.Cup.eq.Cup_Ite
import Lemma.Set.IffInS_Ico
import Lemma.Set.Cup_UFn.eq.Cup_UFnNeg
import Lemma.Int.Add.eq.Sub_Neg
import Lemma.Set.In_Ico.is.InNeg_Ioc
import Lemma.Set.Ioc.eq.Ico
import Lemma.Int.EqNegNeg
import Lemma.Set.CupIn_Ico.eq.Cup_UFnAdd
open Set Int


@[main]
private lemma main
-- given
  (c a b : ℤ)
  (f : ℤ → Set β) :
-- imply
  ⋃ i ∈ Ico a b, f i = ⋃ i ∈ Ico (c - b + 1) (c - a + 1), f (c - i) := by
-- proof
  -- have h_iff : ∀ x, decide (c - x ∈ Ico a b) ↔ x ∈ Ico (c - b + 1) (c - a + 1) := by
    -- simp [IffInS_Ico c a b]
  -- rw [Cup.eq.Cup_Ite (fun x => decidable_of_iff (h (c - x)).decide (h_iff x))]
  conv_rhs =>
    simp only [Cup.eq.Cup_Ite]
    rw [Cup_UFn.eq.Cup_UFnNeg]
    simp only [Sub_Neg.eq.Add]
    simp only [In_Ico.is.InNeg_Ioc]
    simp only [EqNegNeg]
    simp only [Ioc.eq.Ico]
    simp only [Set.Cup_Ite.eq.Cup]
    rw [CupIn_Ico.eq.Cup_UFnAdd (-c)]
    simp
  aesop


-- created on 2025-08-04
-- updated on 2025-09-30

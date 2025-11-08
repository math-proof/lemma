import Lemma.Int.CoeSub.eq.SubCoeS
import Lemma.Int.Ceil.eq.FloorDivSub_Sign
import Lemma.Int.CoeAdd.eq.AddCoeS
open Int


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]
  {n d : ℤ} :
-- imply
  ⌊n / (d : α)⌋ = ⌈(n - d + sign d) / (d : α)⌉ := by
-- proof
  rw [SubCoeS.eq.CoeSub]
  rw [AddCoeS.eq.CoeAdd]
  rw [Ceil.eq.FloorDivSub_Sign]
  simp
  ring_nf


-- created on 2025-04-04
-- updated on 2025-05-04

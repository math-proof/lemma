import Lemma.Algebra.CoeSub.eq.SubCoeS
import Lemma.Algebra.Ceil.eq.FloorDivSub_Sign
import Lemma.Algebra.CoeAdd.eq.AddCoeS
open Algebra


@[main]
private lemma main
  {n d : ℤ} :
-- imply
  ⌊n / (d : ℚ)⌋ = ⌈(n - d + sign d) / (d : ℚ)⌉ := by
-- proof
  rw [SubCoeS.eq.CoeSub.int]
  rw [AddCoeS.eq.CoeAdd.int]
  rw [Ceil.eq.FloorDivSub_Sign]
  simp
  ring_nf


-- created on 2025-04-04
-- updated on 2025-05-04

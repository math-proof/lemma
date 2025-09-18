import Lemma.Set.CupIn_Ico.eq.Cup_UfnAdd
import Lemma.Algebra.Sub.eq.Add_Neg
import Lemma.Algebra.Add.eq.Sub_Neg
open Set Algebra


@[main]
private lemma main
  [OrderedAddCommGroup ι]
-- given
  (a b d : ι)
  (f : ι → Set β) :
-- imply
  ⋃ n ∈ Ico a b, f n = ⋃ n ∈ Ico (a + d) (b + d), f (n - d) := by
-- proof
  rw [CupIn_Ico.eq.Cup_UfnAdd (d := -d)]
  simp only [Add_Neg.eq.Sub]
  simp only [Sub_Neg.eq.Add]


-- created on 2025-08-04

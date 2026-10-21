import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothMvL1_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  (P Q : MvPolynomial (Fin m) ℤ) :
-- imply
  rothMvL1 (P + Q) ≤ rothMvL1 P + rothMvL1 Q := by
-- proof
  classical
  unfold rothMvL1
  have sum_superset (f : Finsupp (RothMvIndex m) ℤ)
    (s : Finset (RothMvIndex m)) (hfs : f.support ⊆ s) :
    rothFinsuppL1 f = ∑ a ∈ s, (f a).natAbs := by
    unfold rothFinsuppL1
    apply Finset.sum_subset hfs
    intro a _ hnot
    rw [Finsupp.notMem_support_iff.mp hnot]
    simp
  let s := P.coeff.support ∪ Q.coeff.support
  have hPQ : (P.coeff + Q.coeff).support ⊆ s := Finsupp.support_add
  rw [show (P + Q).coeff = P.coeff + Q.coeff from rfl]
  rw [sum_superset (P.coeff + Q.coeff) s hPQ]
  rw [sum_superset P.coeff s Finset.subset_union_left]
  rw [sum_superset Q.coeff s Finset.subset_union_right]
  rw [← Finset.sum_add_distrib]
  gcongr with a _
  exact Int.natAbs_add_le _ _


-- created on 2026-10-21

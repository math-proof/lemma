import Mathlib
import Lemma.Fin.RothMvHasse0.eq.Zero.of.RothMvIndex
import Lemma.Fin.RothMvHasseAdd.eq.AddRothSMvHasse.of.RothMvIndex
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothMvHasse_finset_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ} [CommSemiring R]
  (s : Finset ι) (i : RothMvIndex m)
  (P : ι → MvPolynomial (Fin m) R) :
-- imply
  rothMvHasse i (∑ a ∈ s, P a) = ∑ a ∈ s, rothMvHasse i (P a) := by
-- proof
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [RothMvHasse0.eq.Zero.of.RothMvIndex]
  | @insert a s ha ih =>
    simp [ha, RothMvHasseAdd.eq.AddRothSMvHasse.of.RothMvIndex, ih]


-- created on 2026-10-21

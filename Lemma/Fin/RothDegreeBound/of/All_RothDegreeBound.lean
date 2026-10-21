import Mathlib
import Lemma.Fin.RothDegreeBoundSMul
import Lemma.Fin.RothDegreeBound_ProdMulCard.of.All_RothDegreeBound
import Lemma.Fin.RothDegreeBound_Sum.of.All_RothDegreeBound
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothDegreeBound_det](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m k : ℕ}
  (M : Matrix (Fin k) (Fin k) (MvPolynomial (Fin m) ℤ))
  (r : Fin m → ℕ)
-- given
  (hM : ∀ s t, rothDegreeBound (M s t) r) :
-- imply
  rothDegreeBound M.det (fun h ↦ k * r h) := by
-- proof
  classical
  rw [Matrix.det_apply]
  apply RothDegreeBound_Sum.of.All_RothDegreeBound Finset.univ
  intro σ _
  apply RothDegreeBoundSMul
  simpa using RothDegreeBound_ProdMulCard.of.All_RothDegreeBound Finset.univ
    (fun t _ ↦ hM (σ t) t)


-- created on 2026-10-21

import Mathlib
import Lemma.Fin.Any_And_Det_RothMvHasse.ne.Zero.of.All_RothKroneckerBounded.LinearIndependent.Gt_1
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[roth_exists_generalized_wronskian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m k : ℕ}
  (f : Fin k → MvPolynomial (Fin m) ℚ) (r : Fin m → ℕ)
-- given
  (hf : LinearIndependent ℚ f)
  (hdeg : ∀ j, rothDegreeBoundOver (f j) r) :
-- imply
  ∃ i : Fin k → RothMvIndex m,
    (∀ s, rothMvOrder (i s) ≤ s) ∧
      (Matrix.det fun s j ↦ rothMvHasse (i s) (f j)) ≠ 0 := by
-- proof
  classical
  let D := 2 + ∑ h, r h
  refine
    Any_And_Det_RothMvHasse.ne.Zero.of.All_RothKroneckerBounded.LinearIndependent.Gt_1
      (D := D) f ?_ hf ?_
  ·
    dsimp [D]
    omega
  ·
    intro j i hi h
    have hir := hdeg j i hi h
    have hrsum : r h ≤ ∑ t, r t :=
      Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ h)
    dsimp [D]
    omega


-- created on 2026-10-21

import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.ShermanHlam
open StatMech StatMech.Onsager


/--
[ons_edgeWeight_ofFn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanHlam.lean)
-/
@[path]
private lemma ons_edgeWeight_ofFn_eq
  {Λ : Matrix E E ℂ}
  {m : ℕ}
  {f : Fin (m + 1) → E} :
-- imply
  ons_edgeWeight Λ (List.ofFn f) = ∏ i : Fin m, Λ (f i.castSucc) (f i.succ) := by
-- proof
  apply StatMech.Onsager.ons_edgeWeight_ofFn Λ m f

/--
[ons_snoc_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanHlam.lean)
-/
@[path]
private lemma ons_snoc_succ_eq
  {n : ℕ}
  {v : Fin (n + 1) → E}
  {i : Fin (n + 1)} :
-- imply
  (Fin.snoc v (v 0) : Fin (n + 2) → E) i.succ = v (i + 1) := by
-- proof
  apply StatMech.Onsager.ons_snoc_succ v i

/--
[ons_loopWeight_eq_edgeWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanHlam.lean)
-/
@[path]
private lemma ons_loopWeight_eq_edgeWeight_eq
  [Fintype E]
  [DecidableEq E]
  {Λ : Matrix E E ℂ}
  {n : ℕ}
  {v : Fin (n + 1) → E} :
-- imply
  ons_loopWeight Λ v = ons_edgeWeight Λ (List.ofFn v ++ [v 0]) := by
-- proof
  apply StatMech.Onsager.ons_loopWeight_eq_edgeWeight Λ v

/--
[ons_loopWeight_eq_firstReturn_prod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanHlam.lean)
-/
@[path]
private lemma ons_loopWeight_eq_firstReturn_prod_eq
  [Fintype E]
  [DecidableEq E]
  {Λ : Matrix E E ℂ}
  {n : ℕ}
  {e : E}
  {v : Fin (n + 1) → E} :
-- imply
  ons_loopWeight Λ v = ((ons_firstReturnSplit e (List.ofFn v ++ [v 0])).map (ons_edgeWeight Λ)).prod := by
-- proof
  apply StatMech.Onsager.ons_loopWeight_eq_firstReturn_prod Λ e v

/--
[ons_summable_bucketE_of_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanHlam.lean)
-/
@[path]
private lemma ons_summable_bucketE_of_count_eq
  {L : ℕ}
  [NeZero L]
  {x ω : ℂ}
  {e : ons_Dart L}
  {z : ℂ}
-- given
  (hz : ‖z‖ < 1)
  (hcount : ∀ n : ℕ, ons_bucketE L x ω e n = z ^ (n + 1)) :
-- imply
  Summable (fun n : ℕ => ons_bucketE L x ω e n / ((n : ℂ) + 1)) := by
-- proof
  apply StatMech.Onsager.ons_summable_bucketE_of_count x ω e hz hcount

/--
[ons_hlam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanHlam.lean)
-/
@[path]
private lemma ons_hlam_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {x ω : ℂ}
  {e : ons_Dart L}
  {z : ℂ}
-- given
  (hz : ‖z‖ < 1)
  (hcount : ∀ n : ℕ, ons_bucketE L x ω e n = z ^ (n + 1)) :
-- imply
  ∃ lam : ℂ, Complex.exp (- ∑' n : ℕ, ons_bucketE L x ω e n / ((n : ℂ) + 1)) = 1 - lam := by
-- proof
  apply StatMech.Onsager.ons_hlam x ω e hz hcount

/--
[ons_det_final_of_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanHlam.lean)
-/
@[path]
private lemma ons_det_final_of_count_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {x ω : ℂ}
  {e : ons_Dart L}
  {z : ℂ}
-- given
  (hω : ω ^ 2 = Complex.I)
  (hspec : ∀ α ∈ (ons_KWmat L x ω).charpoly.roots, ‖α‖ < 1)
  (hz : ‖z‖ < 1)
  (hcount : ∀ n : ℕ, ons_bucketE L x ω e n = z ^ (n + 1))
  (hN : Summable (fun n : ℕ => ons_bucketN L x ω e n / ((n : ℂ) + 1))) :
-- imply
  (1 - ons_KWmat L x ω).det = Complex.exp (- ∑' n : ℕ, ons_bucketN L x ω e n / ((n : ℂ) + 1)) * (1 - z) ^ 2 := by
-- proof
  apply StatMech.Onsager.ons_det_final_of_count x ω hω e hspec hz hcount hN


-- created on 2026-10-23

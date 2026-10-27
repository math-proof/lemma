import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.ShermanAssembly3
open StatMech StatMech.Onsager


/--
[ons_KW_loopSum_two_bucket](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanAssembly3.lean)
-/
@[path]
private lemma ons_KW_loopSum_two_bucket_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {n : ℕ}
  {x ω : ℂ}
  {e : ons_Dart L}
-- given
  (hω : ω ^ 2 = Complex.I) :
-- imply
  (∑ v : Fin (n + 1) → ons_Dart L, ons_loopWeight (ons_KWmat L x ω) v) = 2 * ons_bucketE L x ω e n + ons_bucketN L x ω e n := by
-- proof
  apply StatMech.Onsager.ons_KW_loopSum_two_bucket x ω hω e

/--
[ons_det_eq_two_bucket_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanAssembly3.lean)
-/
@[path]
private lemma ons_det_eq_two_bucket_exp_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {x ω : ℂ}
  {e : ons_Dart L}
-- given
  (hω : ω ^ 2 = Complex.I)
  (hspec : ∀ α ∈ (ons_KWmat L x ω).charpoly.roots, ‖α‖ < 1) :
-- imply
  (1 - ons_KWmat L x ω).det = Complex.exp (- ∑' n : ℕ, (2 * ons_bucketE L x ω e n + ons_bucketN L x ω e n) / ((n : ℂ) + 1)) := by
-- proof
  apply StatMech.Onsager.ons_det_eq_two_bucket_exp x ω hω e hspec

/--
[ons_det_eq_A_mul_bucket](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanAssembly3.lean)
-/
@[path]
private lemma ons_det_eq_A_mul_bucket_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {x ω : ℂ}
  {e : ons_Dart L}
-- given
  (hω : ω ^ 2 = Complex.I)
  (hspec : ∀ α ∈ (ons_KWmat L x ω).charpoly.roots, ‖α‖ < 1)
  (hB : Summable (fun n : ℕ => ons_bucketE L x ω e n / ((n : ℂ) + 1)))
  (hN : Summable (fun n : ℕ => ons_bucketN L x ω e n / ((n : ℂ) + 1))) :
-- imply
  (1 - ons_KWmat L x ω).det = Complex.exp (- ∑' n : ℕ, ons_bucketN L x ω e n / ((n : ℂ) + 1)) * Complex.exp (-2 * ∑' n : ℕ, ons_bucketE L x ω e n / ((n : ℂ) + 1)) := by
-- proof
  apply StatMech.Onsager.ons_det_eq_A_mul_bucket x ω hω e hspec hB hN

/--
[ons_det_eq_A_mul_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanAssembly3.lean)
-/
@[path]
private lemma ons_det_eq_A_mul_sq_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {x ω : ℂ}
  {e : ons_Dart L}
  {lam : ℂ}
-- given
  (hω : ω ^ 2 = Complex.I)
  (hspec : ∀ α ∈ (ons_KWmat L x ω).charpoly.roots, ‖α‖ < 1)
  (hB : Summable (fun n : ℕ => ons_bucketE L x ω e n / ((n : ℂ) + 1)))
  (hN : Summable (fun n : ℕ => ons_bucketN L x ω e n / ((n : ℂ) + 1)))
  (hlam : Complex.exp (- ∑' n : ℕ, ons_bucketE L x ω e n / ((n : ℂ) + 1)) = 1 - lam) :
-- imply
  (1 - ons_KWmat L x ω).det = Complex.exp (- ∑' n : ℕ, ons_bucketN L x ω e n / ((n : ℂ) + 1)) * (1 - lam) ^ 2 := by
-- proof
  apply StatMech.Onsager.ons_det_eq_A_mul_sq x ω hω e hspec hB hN lam hlam


-- created on 2026-10-23

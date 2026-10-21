import Mathlib
import Lemma.Fin.RothMvWeight_Mul.eq.DivRothMvWeight.of.All_Gt_0.Gt_0.RothMvIndex
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothMvVanishesBelow_mul_weights](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m k : ℕ} [CommRing R]
  {P : MvPolynomial (Fin m) R} {x : Fin m → R} {r : Fin m → ℕ} {t : ℝ}
-- given
  (hP : rothMvVanishesBelow P x r t)
  (hk : 0 < k)
  (hr : ∀ h, 0 < r h) :
-- imply
  rothMvVanishesBelow P x (fun h ↦ k * r h) (t / k) := by
-- proof
  intro i hi
  apply hP i
  rw [RothMvWeight_Mul.eq.DivRothMvWeight.of.All_Gt_0.Gt_0.RothMvIndex r i hk hr] at hi
  exact (div_lt_div_iff_of_pos_right (by exact_mod_cast hk)).mp hi


-- created on 2026-10-21

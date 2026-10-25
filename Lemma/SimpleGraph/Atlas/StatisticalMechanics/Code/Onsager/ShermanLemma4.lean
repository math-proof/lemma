import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.ShermanLemma4.Part3
open StatMech StatMech.Onsager


/--
[ons_cyclicShift_iterate_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma4.lean)
-/
@[path]
private lemma ons_cyclicShift_iterate_apply_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {v : Fin n → E}
  {j : ℕ} :
-- imply
  ons_cyclicShift^[j] v = fun k => v (k + Fin.ofNat n j) := by
-- proof
  apply StatMech.Onsager.ons_cyclicShift_iterate_apply v j

/--
[ons_cyclicShift_iterate_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma4.lean)
-/
@[path]
private lemma ons_cyclicShift_iterate_self_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {v : Fin n → E} :
-- imply
  ons_cyclicShift^[n] v = v := by
-- proof
  apply StatMech.Onsager.ons_cyclicShift_iterate_self v

/--
[ons_cyclicShift_iterate_eq_id](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma4.lean)
-/
@[path]
private lemma ons_cyclicShift_iterate_eq_id_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  [NeZero n] :
-- imply
  ons_cyclicShift^[n] = (id : (Fin n → E) → Fin n → E) := by
-- proof
  apply StatMech.Onsager.ons_cyclicShift_iterate_eq_id

/--
[ons_cyclicShift_iterate_mul_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma4.lean)
-/
@[path]
private lemma ons_cyclicShift_iterate_mul_self_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {v : Fin n → E}
  {j : ℕ} :
-- imply
  ons_cyclicShift^[n * j] v = v := by
-- proof
  apply StatMech.Onsager.ons_cyclicShift_iterate_mul_self v j

/--
[ons_cyclicShift_iterate_mod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma4.lean)
-/
@[path]
private lemma ons_cyclicShift_iterate_mod_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {v : Fin n → E}
  {j : ℕ} :
-- imply
  ons_cyclicShift^[j % n] v = ons_cyclicShift^[j] v := by
-- proof
  apply StatMech.Onsager.ons_cyclicShift_iterate_mod v j

/--
[ons_rep_rel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma4.lean)
-/
@[path]
private lemma ons_rep_rel_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {v : Fin n → E} :
-- imply
  (ons_orbitSetoid E n).r (ons_rep v) v := by
-- proof
  apply StatMech.Onsager.ons_rep_rel v

/--
[ons_iterate_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma4.lean)
-/
@[path]
private lemma ons_iterate_inv_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {f : (Fin n → E) → ℂ}
  {v : Fin n → E}
  {j : ℕ}
-- given
  (hf : ∀ v, f (ons_cyclicShift v) = f v) :
-- imply
  f (ons_cyclicShift^[j] v) = f v := by
-- proof
  apply StatMech.Onsager.ons_iterate_inv hf v j

/--
[ons_eq_of_rel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma4.lean)
-/
@[path]
private lemma ons_eq_of_rel_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {f : (Fin n → E) → ℂ}
  {v w : Fin n → E}
-- given
  (hf : ∀ v, f (ons_cyclicShift v) = f v)
  (h : (ons_orbitSetoid E n).r v w) :
-- imply
  f v = f w := by
-- proof
  apply StatMech.Onsager.ons_eq_of_rel hf h

/--
[ons_sum_fiberwise_orbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma4.lean)
-/
@[path]
private lemma ons_sum_fiberwise_orbit_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {f : (Fin n → E) → ℂ}
-- given
  (hf : ∀ v, f (ons_cyclicShift v) = f v) :
-- imply
  ∑ v : Fin n → E, f v = ∑ r : Fin n → E, (ons_orbitCard r : ℂ) * f r := by
-- proof
  apply StatMech.Onsager.ons_sum_fiberwise_orbit hf

/--
[ons_sum_loopWeight_orbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma4.lean)
-/
@[path]
private lemma ons_sum_loopWeight_orbit_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {Λ : Matrix E E ℂ} :
-- imply
  ∑ v : Fin n → E, ons_loopWeight Λ v = ∑ r : Fin n → E, (ons_orbitCard r : ℂ) * ons_loopWeight Λ r := by
-- proof
  apply StatMech.Onsager.ons_sum_loopWeight_orbit Λ

/--
[ons_hasSum_shifted_pow_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma4.lean)
-/
@[path]
private lemma ons_hasSum_shifted_pow_div_eq
  {z : ℂ}
-- given
  (hz : ‖z‖ < 1) :
-- imply
  HasSum (fun k : ℕ => z ^ (k + 1) / (k + 1)) (-Complex.log (1 - z)) := by
-- proof
  apply StatMech.Onsager.ons_hasSum_shifted_pow_div hz

/--
[ons_tsum_shifted_pow_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma4.lean)
-/
@[path]
private lemma ons_tsum_shifted_pow_div_eq
  {z : ℂ}
-- given
  (hz : ‖z‖ < 1) :
-- imply
  ∑' k : ℕ, z ^ (k + 1) / (k + 1) = -Complex.log (1 - z) := by
-- proof
  apply StatMech.Onsager.ons_tsum_shifted_pow_div hz


-- created on 2026-10-23

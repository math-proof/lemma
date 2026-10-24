import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.ShermanLemma4Return
open StatMech StatMech.Onsager


/--
[ons_one_sub_ne_zero_of_norm_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma4Return.lean)
-/
@[path]
private lemma ons_one_sub_ne_zero_of_norm_lt_one_eq
  {z : ℂ}
-- given
  (hz : ‖z‖ < 1) :
-- imply
  (1 : ℂ) - z ≠ 0 := by
-- proof
  apply StatMech.Onsager.ons_one_sub_ne_zero_of_norm_lt_one hz

/--
[ons_lemma4_geometric](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma4Return.lean)
-/
@[path]
private lemma ons_lemma4_geometric_eq
  {z : ℂ}
-- given
  (hz : ‖z‖ < 1) :
-- imply
  ∑' k : ℕ, z ^ (k + 1) / (k + 1) = -Complex.log (1 - z) := by
-- proof
  apply StatMech.Onsager.ons_lemma4_geometric hz

/--
[ons_lemma4_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma4Return.lean)
-/
@[path]
private lemma ons_lemma4_exp_eq
  {z : ℂ}
-- given
  (hz : ‖z‖ < 1) :
-- imply
  Complex.exp (-(∑' k : ℕ, z ^ (k + 1) / (k + 1))) = 1 - z := by
-- proof
  apply StatMech.Onsager.ons_lemma4_exp hz

/--
[ons_pow_eq_sum_tuple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma4Return.lean)
-/
@[path]
private lemma ons_pow_eq_sum_tuple_eq
  [DecidableEq α]
  {S : Finset α}
  {wt : α → ℂ}
  {k : ℕ} :
-- imply
  (∑ s ∈ S, wt s) ^ k = ∑ p ∈ Fintype.piFinset (fun _ : Fin k => S), ∏ i : Fin k, wt (p i) := by
-- proof
  apply StatMech.Onsager.ons_pow_eq_sum_tuple S wt k

/--
[ons_firstReturn_root](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma4Return.lean)
-/
@[path]
private lemma ons_firstReturn_root_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {e : E}
  {rev : E → E}
  {v : Fin n → E}
-- given
  (h : ons_isFirstReturn e rev v) :
-- imply
  v 0 = e := by
-- proof
  apply StatMech.Onsager.ons_firstReturn_root h

/--
[ons_firstReturn_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma4Return.lean)
-/
@[path]
private lemma ons_firstReturn_unique_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {e : E}
  {rev : E → E}
  {v : Fin n → E}
  {k : Fin n}
-- given
  (h : ons_isFirstReturn e rev v)
  (hk : k ≠ 0) :
-- imply
  v k ≠ e := by
-- proof
  apply StatMech.Onsager.ons_firstReturn_unique h hk

/--
[ons_firstReturn_avoids](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma4Return.lean)
-/
@[path]
private lemma ons_firstReturn_avoids_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {e : E}
  {rev : E → E}
  {v : Fin n → E}
  {k : Fin n}
-- given
  (h : ons_isFirstReturn e rev v) :
-- imply
  v k ≠ rev e := by
-- proof
  apply StatMech.Onsager.ons_firstReturn_avoids h k

/--
[ons_firstReturn_visits_once](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma4Return.lean)
-/
@[path]
private lemma ons_firstReturn_visits_once_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  [DecidableEq (Fin n → E)]
  {e : E}
  {rev : E → E}
  {v : Fin n → E}
-- given
  (h : ons_isFirstReturn e rev v) :
-- imply
  (Finset.univ.filter (fun k : Fin n => v k = e)) = {0} := by
-- proof
  apply StatMech.Onsager.ons_firstReturn_visits_once h

/--
[ons_mem_rootedAvoiding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma4Return.lean)
-/
@[path]
private lemma ons_mem_rootedAvoiding_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {e : E}
  {rev : E → E}
  {v : Fin n → E} :
-- imply
  v ∈ ons_rootedAvoiding (n := n) e rev ↔ v 0 = e ∧ (∀ k : Fin n, v k ≠ rev e) := by
-- proof
  apply StatMech.Onsager.ons_mem_rootedAvoiding e rev v

/--
[ons_firstReturn_mem_rootedAvoiding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma4Return.lean)
-/
@[path]
private lemma ons_firstReturn_mem_rootedAvoiding_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {e : E}
  {rev : E → E}
  {v : Fin n → E}
-- given
  (h : ons_isFirstReturn e rev v) :
-- imply
  v ∈ ons_rootedAvoiding (n := n) e rev := by
-- proof
  apply StatMech.Onsager.ons_firstReturn_mem_rootedAvoiding h

/--
[ons_append_succ_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma4Return.lean)
-/
@[path]
private lemma ons_append_succ_left_eq
  {n m : ℕ}
  [NeZero n]
  [NeZero m]
  {u : Fin n → E}
  {w : Fin m → E}
  {i : Fin n}
-- given
  (hw : w 0 = u 0) :
-- imply
  Fin.append u w ((Fin.castAdd m i) + 1) = u (i + 1) := by
-- proof
  apply StatMech.Onsager.ons_append_succ_left u w hw i

/--
[ons_append_succ_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma4Return.lean)
-/
@[path]
private lemma ons_append_succ_right_eq
  {n m : ℕ}
  [NeZero n]
  [NeZero m]
  {u : Fin n → E}
  {w : Fin m → E}
  {i : Fin m}
-- given
  (hw : w 0 = u 0) :
-- imply
  Fin.append u w ((Fin.natAdd n i) + 1) = w (i + 1) := by
-- proof
  apply StatMech.Onsager.ons_append_succ_right u w hw i

/--
[ons_loopWeight_concat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma4Return.lean)
-/
@[path]
private lemma ons_loopWeight_concat_eq
  {n m : ℕ}
  [NeZero n]
  [NeZero m]
  [Fintype E]
  [DecidableEq E]
  {Λ : Matrix E E ℂ}
  {u : Fin n → E}
  {w : Fin m → E}
-- given
  (hw : w 0 = u 0) :
-- imply
  haveI : NeZero (n + m) := by
-- proof
  apply StatMech.Onsager.ons_loopWeight_concat Λ u w hw

/--
[ons_lemma4_of_factorization](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma4Return.lean)
-/
@[path]
private lemma ons_lemma4_of_factorization_eq
  {z : ℂ}
  {perK : ℕ → ℂ}
-- given
  (hz : ‖z‖ < 1)
  (hcount : ∀ k : ℕ, perK k = z ^ (k + 1)) :
-- imply
  (∑' k : ℕ, perK k / (k + 1)) = -Complex.log (1 - z) ∧ Complex.exp (-(∑' k : ℕ, perK k / (k + 1))) = 1 - z := by
-- proof
  apply StatMech.Onsager.ons_lemma4_of_factorization hz perK hcount


-- created on 2026-10-23

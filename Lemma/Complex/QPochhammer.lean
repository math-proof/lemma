import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.SpecialFunctions.QPochhammer
open unit disk.


namespace MetaMathlibExt.QPochhammer

/--
[QPochhammer](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/QPochhammer.lean)
-/
@[path]
lemma qPochhammerInf_zero_left
-- given
  (q : ℂ)
  (hq : ‖q‖ < 1) :
-- imply
  MetaMathlibExt.QPochhammer.qPochhammerInf 0 q hq = 1 := by
-- proof
  simp [qPochhammerInf, qPochhammerInfRaw]

end MetaMathlibExt.QPochhammer

namespace MetaMathlibExt.QPochhammer

/--
[QPochhammer](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/QPochhammer.lean)
-/
@[path]
lemma hasProd_qPochhammerInf
-- given
  (a q : ℂ)
  (hq : ‖q‖ < 1) :
-- imply
  HasProd (fun n : ℕ => (1 - a * q ^ n))
    (MetaMathlibExt.QPochhammer.qPochhammerInf a q hq) := by
-- proof
  have hs : Summable (fun n : ℕ => q ^ n) :=
    summable_geometric_of_norm_lt_one hq
  have hsa : Summable (fun n : ℕ => (-a) * q ^ n) := hs.mul_left (-a)
  have hm : Multipliable (fun n : ℕ => 1 + (-a) * q ^ n) :=
    Complex.multipliable_one_add_of_summable hsa
  simpa [qPochhammerInf, qPochhammerInfRaw, sub_eq_add_neg] using hm.hasProd

end MetaMathlibExt.QPochhammer

namespace MetaMathlibExt.QPochhammer

/--
[QPochhammer](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/QPochhammer.lean)
-/
@[path]
lemma qPochhammerInf_one_zero
-- given
  (hq : ‖(0 : ℂ)‖ < 1) :
-- imply
  MetaMathlibExt.QPochhammer.qPochhammerInf 1 0 hq = 0 := by
-- proof
  have hp := hasProd_qPochhammerInf 1 0 (by simp)
  have hz : HasProd (fun n : ℕ => (1 - (1 : ℂ) * (0 : ℂ) ^ n)) 0 :=
    hasProd_zero_of_exists_eq_zero ⟨0, by simp⟩
  exact hp.unique hz

end MetaMathlibExt.QPochhammer

namespace MetaMathlibExt.QPochhammer

/--
[QPochhammer](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/QPochhammer.lean)
-/
@[path]
lemma qPochhammerInfRaw_two_one
-- imply
  MetaMathlibExt.QPochhammer.qPochhammerInfRaw 2 1 = 1 := by
-- proof
  have hfactor : ∀ n : ℕ, (1 - (2 : ℂ) * (1 : ℂ) ^ n) = -1 := by
    intro n
    simp only [one_pow, mul_one]
    norm_num
  have hnm : ¬Multipliable (fun n : ℕ => (1 - (2 : ℂ) * (1 : ℂ) ^ n)) := by
    intro hm
    have hm1 : Multipliable (fun _ : ℕ => (-1 : ℂ)) := by
      simpa only [hfactor] using hm
    obtain ⟨m, hmlim⟩ := hm1
    have hlim : Filter.Tendsto (fun n : ℕ => (-1 : ℂ) ^ n) Filter.atTop (nhds m) := by
      have h := hmlim.tendsto_prod_nat
      simpa only [Finset.prod_const, Finset.card_range] using h
    have hshift : Filter.Tendsto (fun n : ℕ => (-1 : ℂ) ^ (n + 1)) Filter.atTop (nhds m) :=
      hlim.comp (Filter.tendsto_add_atTop_nat 1)
    have hnegseq : (fun n : ℕ => (-1 : ℂ) ^ (n + 1)) = fun n : ℕ => -((-1 : ℂ) ^ n) := by
      funext n
      rw [pow_succ]
      ring
    rw [hnegseq] at hshift
    have hmeq : m = -m := tendsto_nhds_unique hshift hlim.neg
    have hm0 : m = 0 := by linear_combination hmeq / 2
    have hmul : Filter.Tendsto (fun n : ℕ => (-1 : ℂ) ^ n * (-1 : ℂ) ^ n) Filter.atTop
      (nhds (m * m)) :=
      hlim.mul hlim
    have hone : (fun n : ℕ => (-1 : ℂ) ^ n * (-1 : ℂ) ^ n) = fun _ : ℕ => (1 : ℂ) := by
      funext n
      rw [← pow_add]
      exact Even.neg_one_pow ⟨n, rfl⟩
    rw [hone] at hmul
    have hsq : m * m = 1 := tendsto_nhds_unique hmul tendsto_const_nhds
    rw [hm0] at hsq
    norm_num at hsq
  change tprod (fun n : ℕ => (1 - (2 : ℂ) * (1 : ℂ) ^ n)) = 1
  exact tprod_eq_one_of_not_multipliable hnm

end MetaMathlibExt.QPochhammer


-- created on 2026-10-11
-- updated on 2026-10-26

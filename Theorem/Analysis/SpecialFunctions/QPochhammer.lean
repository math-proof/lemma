import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecificLimits.Normed
import Def.Analysis.SpecialFunctions.QPochhammer.Part2
/-!
# Infinite q-Pochhammer products

This file defines the complex infinite q-Pochhammer symbol and proves its
convergence on the open unit disk.

The raw product `qPochhammerInfRaw` is the total `tprod` value, which is `1` by
convention when the factor family is not multipliable. The canonical symbol
`qPochhammerInf` additionally takes convergence evidence `‖q‖ < 1`, so an
out-of-domain `q` cannot be passed silently.

## Main definitions

* `MetaMathlibExt.QPochhammer.qPochhammerInfRaw`
* `MetaMathlibExt.QPochhammer.qPochhammerInf`

## Main statements

* `MetaMathlibExt.QPochhammer.hasProd_qPochhammerInf`
* `MetaMathlibExt.QPochhammer.qPochhammerInfRaw_two_one`
-/


namespace MetaMathlibExt.QPochhammer

/-- With zero first parameter, every q-Pochhammer factor is one. -/
@[simp]
theorem qPochhammerInf_zero_left (q : ℂ) (hq : ‖q‖ < 1) :
    qPochhammerInf 0 q hq = 1 := by
  simp [qPochhammerInf, qPochhammerInfRaw]

/-- Convergence of the complex q-Pochhammer infinite product on the
open unit disk.

Source `2607.10576:D01`: the infinite product `(a;q)_∞` is used under
`‖q‖ < 1`. For complex `a, q` with `‖q‖ < 1` the factor family
`n ↦ 1 - a * q ^ n` satisfies `HasProd` to the named value
`qPochhammerInf a q hq`. No nonvanishing hypothesis is imposed, so
zero-factor cases (product value `0`) are covered. -/
theorem hasProd_qPochhammerInf (a q : ℂ) (hq : ‖q‖ < 1) :
    HasProd (fun n : ℕ => (1 - a * q ^ n)) (qPochhammerInf a q hq) := by
  have hs : Summable (fun n : ℕ => q ^ n) :=
    summable_geometric_of_norm_lt_one hq
  have hsa : Summable (fun n : ℕ => (-a) * q ^ n) := hs.mul_left (-a)
  have hm : Multipliable (fun n : ℕ => 1 + (-a) * q ^ n) :=
    Complex.multipliable_one_add_of_summable hsa
  simpa [qPochhammerInf, qPochhammerInfRaw, sub_eq_add_neg] using hm.hasProd

/-- The first factor vanishes at `(a, q) = (1, 0)`. -/
@[simp]
theorem qPochhammerInf_one_zero : qPochhammerInf 1 0 (by simp) = 0 := by
  have hp := hasProd_qPochhammerInf 1 0 (by simp)
  have hz : HasProd (fun n : ℕ => (1 - (1 : ℂ) * (0 : ℂ) ^ n)) 0 :=
    hasProd_zero_of_exists_eq_zero ⟨0, by simp⟩
  exact hp.unique hz

/-- Regression for the raw product outside the unit disk: the `tprod` fallback.

At `(a, q) = (2, 1)` every factor equals `-1`, so the family is not
multipliable and the total product `qPochhammerInfRaw 2 1` is `1` by the
`tprod` convention (`tprod_eq_one_of_not_multipliable`), not a limit of
partial products. This is exactly the silent wrong-value behaviour that the
gated `qPochhammerInf` (which demands `‖q‖ < 1`) rules out. -/
theorem qPochhammerInfRaw_two_one : qPochhammerInfRaw 2 1 = 1 := by
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

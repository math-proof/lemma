import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.BeffaraDC.Dichotomy
open StatMech StatMech.BeffaraDC


/--
[selfDualPoint_value](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/Dichotomy.lean)
-/
@[path]
private lemma selfDualPoint_value_eq
  {q : ℝ} :
-- imply
  selfDualPoint q = Real.sqrt q / (1 + Real.sqrt q) := by
-- proof
  apply StatMech.BeffaraDC.selfDualPoint_value q

/--
[selfDualPoint_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/Dichotomy.lean)
-/
@[path]
private lemma selfDualPoint_pos_eq
  {q : ℝ}
-- given
  (hq : 0 < q) :
-- imply
  0 < selfDualPoint q := by
-- proof
  apply StatMech.BeffaraDC.selfDualPoint_pos hq

/--
[selfDualPoint_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/Dichotomy.lean)
-/
@[path]
private lemma selfDualPoint_lt_one_eq
  {q : ℝ}
-- given
  (hq : 0 < q) :
-- imply
  selfDualPoint q < 1 := by
-- proof
  apply StatMech.BeffaraDC.selfDualPoint_lt_one hq

/--
[selfDualPoint_dual_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/Dichotomy.lean)
-/
@[path]
private lemma selfDualPoint_dual_eq_eq
  {q : ℝ}
-- given
  (hq : 0 < q) :
-- imply
  dualParam (selfDualPoint q) q = selfDualPoint q := by
-- proof
  apply StatMech.BeffaraDC.selfDualPoint_dual_eq hq

/--
[decay_of_linear_hamming](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/Dichotomy.lean)
-/
@[path]
private lemma decay_of_linear_hamming_eq
  [Fintype E]
  [DecidableEq E]
  {p₁ p₂ : ℝ}
  {A : Set (ConfigSpace E)}
  {a n : ℝ}
-- given
  (hp1 : 0 < p₁)
  (hp12 : p₁ < p₂)
  (hp2 : p₂ < 1)
  (hA : IsIncreasing A)
  (hLinearHamming : a * n ≤ expect p₂ (fun ω => (hammingToSet A ω : ℝ)))
  (hprobOne : prob p₂ A ≤ 1) :
-- imply
  prob p₁ A ≤ Real.exp (- 4 * (p₂ - p₁) * (a * n)) := by
-- proof
  apply StatMech.BeffaraDC.decay_of_linear_hamming hp1 hp12 hp2 A hA hLinearHamming hprobOne

/--
[decay_rate_of_linear_hamming](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/Dichotomy.lean)
-/
@[path]
private lemma decay_rate_of_linear_hamming_eq
  [Fintype E]
  [DecidableEq E]
  {p₁ p₂ : ℝ}
  {A : Set (ConfigSpace E)}
  {a n : ℝ}
-- given
  (hp1 : 0 < p₁)
  (hp12 : p₁ < p₂)
  (hp2 : p₂ < 1)
  (hA : IsIncreasing A)
  (ha : 0 < a)
  (hn : 0 ≤ n)
  (hLinearHamming : a * n ≤ expect p₂ (fun ω => (hammingToSet A ω : ℝ)))
  (hprobOne : prob p₂ A ≤ 1) :
-- imply
  0 < 4 * (p₂ - p₁) * a ∧ prob p₁ A ≤ Real.exp (- (4 * (p₂ - p₁) * a) * n) := by
-- proof
  apply StatMech.BeffaraDC.decay_rate_of_linear_hamming hp1 hp12 hp2 A hA ha hn hLinearHamming hprobOne

/--
[crossing_dichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/Dichotomy.lean)
-/
@[path]
private lemma crossing_dichotomy_eq
  [Fintype E]
  [DecidableEq E]
  {q : ℝ}
  {p p₂ : ℝ}
  {A : ℕ → Set (ConfigSpace E)}
  {a b : ℝ}
-- given
  (hq : 1 ≤ q)
  (hp0 : 0 < p)
  (hp_sd : p < selfDualPoint q)
  (hsd_p2 : selfDualPoint q ≤ p₂)
  (hp2 : p₂ < 1)
  (hA : ∀ n, IsIncreasing (A n))
  (ha : 0 < a)
  (hb : 0 < b)
  (hprobOne : ∀ n : ℕ, prob p₂ (A n) ≤ 1)
  (hLinearHamming : ∀ n : ℕ, a * (n : ℝ) ≤ expect p₂ (fun ω => (hammingToSet (A n) ω : ℝ)))
  (hRSWLowerBound : ∀ n : ℕ, b ≤ prob (selfDualPoint q) (A n)) :
-- imply
  ∃ c > 0, (∀ n : ℕ, prob p (A n) ≤ Real.exp (- c * (n : ℝ))) ∧ (0 < b ∧ ∀ n : ℕ, b ≤ prob (selfDualPoint q) (A n)) := by
-- proof
  apply StatMech.BeffaraDC.crossing_dichotomy hq hp0 hp_sd hsd_p2 hp2 A hA ha hb hprobOne hLinearHamming hRSWLowerBound

/--
[beffaraDC_dichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/Dichotomy.lean)
-/
@[path]
private lemma beffaraDC_dichotomy_eq
  [Fintype E]
  [DecidableEq E]
  {q : ℝ}
  {p p₂ : ℝ}
  {A : ℕ → Set (ConfigSpace E)}
  {a b : ℝ}
-- given
  (hq : 1 ≤ q)
  (hp0 : 0 < p)
  (hp_sd : p < Real.sqrt q / (1 + Real.sqrt q))
  (hsd_p2 : Real.sqrt q / (1 + Real.sqrt q) ≤ p₂)
  (hp2 : p₂ < 1)
  (hA : ∀ n, IsIncreasing (A n))
  (ha : 0 < a)
  (hb : 0 < b)
  (hprobOne : ∀ n : ℕ, prob p₂ (A n) ≤ 1)
  (hLinearHamming : ∀ n : ℕ, a * (n : ℝ) ≤ expect p₂ (fun ω => (hammingToSet (A n) ω : ℝ)))
  (hRSWLowerBound : ∀ n : ℕ, b ≤ prob (Real.sqrt q / (1 + Real.sqrt q)) (A n)) :
-- imply
  ∃ c > 0, (∀ n : ℕ, prob p (A n) ≤ Real.exp (- c * (n : ℝ))) ∧ (0 < b ∧ ∀ n : ℕ, b ≤ prob (Real.sqrt q / (1 + Real.sqrt q)) (A n)) := by
-- proof
  apply StatMech.BeffaraDC.beffaraDC_dichotomy hq hp0 hp_sd hsd_p2 hp2 A hA ha hb hprobOne hLinearHamming hRSWLowerBound


-- created on 2026-10-23

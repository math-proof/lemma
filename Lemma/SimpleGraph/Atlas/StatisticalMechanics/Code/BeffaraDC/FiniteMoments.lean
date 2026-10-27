import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.BeffaraDC.FiniteMoments.Part3
open StatMech StatMech.BeffaraDC


/--
[hammingToSet_le_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/FiniteMoments.lean)
-/
@[path]
private lemma hammingToSet_le_card_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {ω : ConfigSpace E} :
-- imply
  hammingToSet A ω ≤ Fintype.card E := by
-- proof
  apply StatMech.BeffaraDC.hammingToSet_le_card A ω

/--
[hammingToSet_real_le_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/FiniteMoments.lean)
-/
@[path]
private lemma hammingToSet_real_le_card_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {ω : ConfigSpace E} :
-- imply
  (hammingToSet A ω : ℝ) ≤ (Fintype.card E : ℝ) := by
-- proof
  apply StatMech.BeffaraDC.hammingToSet_real_le_card A ω

/--
[expect_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/FiniteMoments.lean)
-/
@[path]
private lemma expect_const_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {c : ℝ} :
-- imply
  expect p (fun _ : ConfigSpace E => c) = c := by
-- proof
  apply StatMech.BeffaraDC.expect_const p c

/--
[expect_le_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/FiniteMoments.lean)
-/
@[path]
private lemma expect_le_const_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {c : ℝ}
  {f : ConfigSpace E → ℝ}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1)
  (h : ∀ ω, f ω ≤ c) :
-- imply
  expect p f ≤ c := by
-- proof
  apply StatMech.BeffaraDC.expect_le_const hp0 hp1 h

/--
[hammingMoment_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/FiniteMoments.lean)
-/
@[path]
private lemma hammingMoment_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {A : Set (ConfigSpace E)}
  {d : ℕ}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1) :
-- imply
  0 ≤ hammingMoment p A d := by
-- proof
  apply StatMech.BeffaraDC.hammingMoment_nonneg hp0 hp1 A d

/--
[hammingMoment_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/FiniteMoments.lean)
-/
@[path]
private lemma hammingMoment_le_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {A : Set (ConfigSpace E)}
  {d : ℕ}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1) :
-- imply
  hammingMoment p A d ≤ (Fintype.card E : ℝ) ^ d := by
-- proof
  apply StatMech.BeffaraDC.hammingMoment_le hp0 hp1 A d

/--
[hammingMoment_lt_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/FiniteMoments.lean)
-/
@[path]
private lemma hammingMoment_lt_top_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {A : Set (ConfigSpace E)}
  {d : ℕ}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1) :
-- imply
  hammingMoment p A d < (Fintype.card E : ℝ) ^ d + 1 := by
-- proof
  apply StatMech.BeffaraDC.hammingMoment_lt_top hp0 hp1 A d

/--
[hammingMoment_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/FiniteMoments.lean)
-/
@[path]
private lemma hammingMoment_le_one_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {A : Set (ConfigSpace E)}
  {d : ℕ}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1)
  (hcard : Fintype.card E ≤ 1) :
-- imply
  hammingMoment p A d ≤ 1 := by
-- proof
  apply StatMech.BeffaraDC.hammingMoment_le_one hp0 hp1 A hcard d

/--
[expHammingMoment_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/FiniteMoments.lean)
-/
@[path]
private lemma expHammingMoment_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {A : Set (ConfigSpace E)}
  {t : ℝ}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1) :
-- imply
  0 ≤ expHammingMoment p A t := by
-- proof
  apply StatMech.BeffaraDC.expHammingMoment_nonneg hp0 hp1 A t

/--
[exp_hammingMoment_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/FiniteMoments.lean)
-/
@[path]
private lemma exp_hammingMoment_le_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {A : Set (ConfigSpace E)}
  {t : ℝ}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1)
  (ht : 0 ≤ t) :
-- imply
  expHammingMoment p A t ≤ Real.exp (t * (Fintype.card E : ℝ)) := by
-- proof
  apply StatMech.BeffaraDC.exp_hammingMoment_le hp0 hp1 A ht

/--
[hammingMoment_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/FiniteMoments.lean)
-/
@[path]
private lemma hammingMoment_one_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {A : Set (ConfigSpace E)} :
-- imply
  hammingMoment p A 1 = expect p (fun ω => (hammingToSet A ω : ℝ)) := by
-- proof
  apply StatMech.BeffaraDC.hammingMoment_one p A

/--
[first_moment_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/FiniteMoments.lean)
-/
@[path]
private lemma first_moment_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {A : Set (ConfigSpace E)}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1) :
-- imply
  0 ≤ expect p (fun ω => (hammingToSet A ω : ℝ)) := by
-- proof
  apply StatMech.BeffaraDC.first_moment_nonneg hp0 hp1 A

/--
[prob_le_first_moment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/FiniteMoments.lean)
-/
@[path]
private lemma prob_le_first_moment_eq
  [Fintype E]
  [DecidableEq E]
  {p₁ p₂ : ℝ}
  {A : Set (ConfigSpace E)}
-- given
  (hp1 : 0 < p₁)
  (hp12 : p₁ < p₂)
  (hp2 : p₂ < 1)
  (hA : IsIncreasing A) :
-- imply
  prob p₁ A ≤ prob p₂ A * Real.exp (- 4 * (p₂ - p₁) * expect p₂ (fun ω => (hammingToSet A ω : ℝ))) := by
-- proof
  apply StatMech.BeffaraDC.prob_le_first_moment hp1 hp12 hp2 A hA


-- created on 2026-10-23

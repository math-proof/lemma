import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.SAW
open StatMech StatMech.Universality


/--
[Subadditive_log_of_submultiplicative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/SAW.lean)
-/
@[path]
private lemma Subadditive_log_of_submultiplicative_eq
  {c : ℕ → ℝ}
-- given
  (hpos : ∀ n, 0 < c n)
  (hsub : Submultiplicative c) :
-- imply
  Subadditive (fun n => Real.log (c n)) := by
-- proof
  apply StatMech.Universality.Subadditive_log_of_submultiplicative hpos hsub

/--
[fekete_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/SAW.lean)
-/
@[path]
private lemma fekete_tendsto_eq
  {x : ℕ → ℝ}
-- given
  (h : Subadditive x)
  (hbdd : BddBelow (Set.range fun n => x n / n)) :
-- imply
  Tendsto (fun n => x n / n) atTop (𝓝 h.lim) := by
-- proof
  apply StatMech.Universality.fekete_tendsto h hbdd

/--
[fekete_lim_eq_iInf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/SAW.lean)
-/
@[path]
private lemma fekete_lim_eq_iInf_eq
  {x : ℕ → ℝ}
-- given
  (h : Subadditive x) :
-- imply
  h.lim = sInf ((fun n : ℕ => x n / n) '' Set.Ici 1) := by
-- proof
  apply StatMech.Universality.fekete_lim_eq_iInf h

/--
[fekete_lim_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/SAW.lean)
-/
@[path]
private lemma fekete_lim_le_eq
  {x : ℕ → ℝ}
  {n : ℕ}
-- given
  (h : Subadditive x)
  (hbdd : BddBelow (Set.range fun n => x n / n))
  (hn : n ≠ 0) :
-- imply
  h.lim ≤ x n / n := by
-- proof
  apply StatMech.Universality.fekete_lim_le h hbdd hn

/--
[bddBelow_log_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/SAW.lean)
-/
@[path]
private lemma bddBelow_log_div_eq
  {c : ℕ → ℝ}
-- given
  (hge : ∀ n, 1 ≤ c n) :
-- imply
  BddBelow (Set.range fun n => Real.log (c n) / n) := by
-- proof
  apply StatMech.Universality.bddBelow_log_div hge

/--
[connectiveConstant_log_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/SAW.lean)
-/
@[path]
private lemma connectiveConstant_log_tendsto_eq
  {c : ℕ → ℝ}
-- given
  (hge : ∀ n, 1 ≤ c n)
  (hsub : Submultiplicative c) :
-- imply
  ∃ L : ℝ, Tendsto (fun n => Real.log (c n) / n) atTop (𝓝 L) := by
-- proof
  apply StatMech.Universality.connectiveConstant_log_tendsto hge hsub

/--
[connectiveConstant_log_eq_iInf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/SAW.lean)
-/
@[path]
private lemma connectiveConstant_log_eq_iInf_eq
  {c : ℕ → ℝ}
-- given
  (hge : ∀ n, 1 ≤ c n)
  (hsub : Submultiplicative c) :
-- imply
  (Subadditive_log_of_submultiplicative (fun n => zero_lt_one.trans_le (hge n)) hsub).lim = sInf ((fun n : ℕ => Real.log (c n) / n) '' Set.Ici 1) := by
-- proof
  apply StatMech.Universality.connectiveConstant_log_eq_iInf hge hsub

/--
[connectiveConstant_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/SAW.lean)
-/
@[path]
private lemma connectiveConstant_tendsto_eq
  {c : ℕ → ℝ}
-- given
  (hge : ∀ n, 1 ≤ c n)
  (hsub : Submultiplicative c) :
-- imply
  ∃ κ : ℝ, 0 < κ ∧ Tendsto (fun n => (c n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 κ) := by
-- proof
  apply StatMech.Universality.connectiveConstant_tendsto hge hsub


-- created on 2026-10-23

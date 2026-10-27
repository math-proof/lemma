import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.FeketeLimit
open MeasureTheory Set Filter Topology Real StatMech StatMech.FK


/--
[fkl_tendsto_div_of_subadditive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FeketeLimit.lean)
-/
@[path]
private lemma fkl_tendsto_div_of_subadditive_eq
  {u : ℕ → ℝ}
  {e : ℕ → ℝ}
  {c : ℝ}
-- given
  (hsub : Subadditive u)
  (hbdd : BddBelow (Set.range fun n => u n / n))
  (hc : c ≠ 0)
  (he : Tendsto (fun n => e n / n) atTop (𝓝 c)) :
-- imply
  Tendsto (fun n => u n / e n) atTop (𝓝 (hsub.lim / c)) := by
-- proof
  apply StatMech.FK.fkl_tendsto_div_of_subadditive u hsub hbdd e c hc he

/--
[fkl_tiltFreeEnergy_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FeketeLimit.lean)
-/
@[path]
private lemma fkl_tiltFreeEnergy_tendsto_eq
  {V : ℕ → Type*}
  [∀ n, Fintype (V n)]
  [∀ n, DecidableEq (V n)]
  {q : ℝ}
  {t : ℝ}
  {c : ℝ}
-- given
  (hq : 0 < q)
  (hE : ∀ n, 0 < (Gn n).edgeFinset.card)
  (hsuper : Subadditive (fun n => - Real.log (fkZ (Gn n) (fsc_logistic t) q)))
  (hbdd : BddBelow (Set.range fun n => (- Real.log (fkZ (Gn n) (fsc_logistic t) q)) / n))
  (hc : c ≠ 0)
  (he : Tendsto (fun n => ((Gn n).edgeFinset.card : ℝ) / n) atTop (𝓝 c)) :
-- imply
  Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) q t) atTop (𝓝 (- (hsuper.lim / c) + Real.log (1 + Real.exp t))) := by
-- proof
  apply StatMech.FK.fkl_tiltFreeEnergy_tendsto q hq t hE hsuper hbdd c hc he

/--
[fkl_fekete_limit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FeketeLimit.lean)
-/
@[path]
private lemma fkl_fekete_limit_eq
  {V : ℕ → Type*}
  [∀ n, Fintype (V n)]
  [∀ n, DecidableEq (V n)]
  {q : ℝ}
  {c : ℝ → ℝ}
-- given
  (hq : 0 < q)
  (hE : ∀ n, 0 < (Gn n).edgeFinset.card)
  (hsuper : ∀ t, Subadditive (fun n => - Real.log (fkZ (Gn n) (fsc_logistic t) q)))
  (hbdd : ∀ t, BddBelow (Set.range fun n => (- Real.log (fkZ (Gn n) (fsc_logistic t) q)) / n))
  (hc : ∀ t, c t ≠ 0)
  (he : ∀ t, Tendsto (fun n => ((Gn n).edgeFinset.card : ℝ) / n) atTop (𝓝 (c t))) :
-- imply
  ∃ g : ℝ → ℝ, (∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) q t) atTop (𝓝 (g t))) ∧ ConvexOn ℝ univ g := by
-- proof
  apply StatMech.FK.fkl_fekete_limit q hq hE hsuper hbdd c hc he

/--
[fkl_subadditive_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FeketeLimit.lean)
-/
@[path]
private lemma fkl_subadditive_zero_eq
  {V : ℕ → Type*}
  [∀ n, Fintype (V n)]
  [∀ n, DecidableEq (V n)] :
-- imply
  Subadditive (fun _ : ℕ => (0:ℝ)) := by
-- proof
  apply StatMech.FK.fkl_subadditive_zero

/--
[fkl_superMultiplicative_satisfiable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FeketeLimit.lean)
-/
@[path]
private lemma fkl_superMultiplicative_satisfiable_eq
  {V : ℕ → Type*}
  [∀ n, Fintype (V n)]
  [∀ n, DecidableEq (V n)] :
-- imply
  ∃ (u : ℕ → ℝ) (hsub : Subadditive u) (e : ℕ → ℝ) (c : ℝ), c ≠ 0 ∧ BddBelow (Set.range fun n => u n / n) ∧ Tendsto (fun n => e n / n) atTop (𝓝 c) ∧ Tendsto (fun n => u n / e n) atTop (𝓝 (hsub.lim / c)) := by
-- proof
  apply StatMech.FK.fkl_superMultiplicative_satisfiable


-- created on 2026-10-23

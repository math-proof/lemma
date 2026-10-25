import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.FKQ2Sharp
open Finset Real Set StatMech StatMech.FK


/--
[mul_one_sub_le_quarter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKQ2Sharp.lean)
-/
@[path]
private lemma mul_one_sub_le_quarter_eq
  {x : ℝ} :
-- imply
  x * (1 - x) ≤ 1 / 4 := by
-- proof
  apply StatMech.FK.mul_one_sub_le_quarter x

/--
[russoPrefactor_ge_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKQ2Sharp.lean)
-/
@[path]
private lemma russoPrefactor_ge_four_eq
  {x : ℝ}
-- given
  (hx0 : 0 < x)
  (hx1 : x < 1) :
-- imply
  (4 : ℝ) ≤ russoPrefactor x := by
-- proof
  apply StatMech.FK.russoPrefactor_ge_four hx0 hx1

/--
[fkProbOf_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKQ2Sharp.lean)
-/
@[path]
private lemma fkProbOf_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 ≤ fkProbOf G p q A := by
-- proof
  apply StatMech.FK.fkProbOf_nonneg G hp hp1 hq A

/--
[fkProbOf_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKQ2Sharp.lean)
-/
@[path]
private lemma fkProbOf_le_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  fkProbOf G p q A ≤ 1 := by
-- proof
  apply StatMech.FK.fkProbOf_le_one G hp hp1 hq A

/--
[pointwise_di_fk_q2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKQ2Sharp.lean)
-/
@[path]
private lemma pointwise_di_fk_q2_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : ℕ}
  {p : ℝ}
  {A : Set (ConfigSpace (Sym2 V))}
  {c₀ D κ : ℝ}
-- given
  (hn : 1 ≤ n)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hc₀ : 0 < c₀)
  (hD : 0 < D)
  (hκ : 0 < κ)
  (hFKcov : (n : ℝ) * c₀ * (fkProbOf G p 2 A * (1 - fkProbOf G p 2 A)) ≤ D * ∑ e ∈ G.edgeFinset, fkCov G p 2 (A.indicator (fun _ => (1 : ℝ))) (coord e))
  (hθub : fkProbOf G p 2 A ≤ 1 - κ) :
-- imply
  (4 * (n : ℝ) * c₀ * κ / D) * fkProbOf G p 2 A ≤ deriv (fun p => fkProbOf G p 2 A) p := by
-- proof
  apply StatMech.FK.pointwise_di_fk_q2 G hn hp hp1 A c₀ D κ hc₀ hD hκ hFKcov hθub

/--
[fk_q2_crossing_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKQ2Sharp.lean)
-/
@[path]
private lemma fk_q2_crossing_decay_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : ℕ}
  {A : Set (ConfigSpace (Sym2 V))}
  {c₀ D κ : ℝ}
  {a b : ℝ}
-- given
  (hn : 1 ≤ n)
  (hc₀ : 0 < c₀)
  (hD : 0 < D)
  (hκ : 0 < κ)
  (hab : a < b)
  (ha0 : 0 < a)
  (hb1 : b < 1)
  (hdiff : ∀ p ∈ Icc a b, HasDerivAt (fun p => fkProbOf G p 2 A) (deriv (fun p => fkProbOf G p 2 A) p) p)
  (hFKcov : ∀ p ∈ Icc a b, (n : ℝ) * c₀ * (fkProbOf G p 2 A * (1 - fkProbOf G p 2 A)) ≤ D * ∑ e ∈ G.edgeFinset, fkCov G p 2 (A.indicator (fun _ => (1 : ℝ))) (coord e))
  (hθub : ∀ p ∈ Icc a b, fkProbOf G p 2 A ≤ 1 - κ) :
-- imply
  fkProbOf G a 2 A ≤ Real.exp (-(4 * (n : ℝ) * c₀ * κ / D * (b - a))) := by
-- proof
  apply StatMech.FK.fk_q2_crossing_decay G hn A c₀ D κ hc₀ hD hκ a b hab ha0 hb1 hdiff hFKcov hθub

/--
[fkTheta_subcritical_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKQ2Sharp.lean)
-/
@[path]
private lemma fkTheta_subcritical_eq_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {c₀ D κ : ℝ}
  {a b : ℝ}
-- given
  (hc₀ : 0 < c₀)
  (hD : 0 < D)
  (hκ : 0 < κ)
  (hab : a < b)
  (ha0 : 0 < a)
  (hb1 : b < 1)
  (Across : ∀ N : ℕ, Set (ConfigSpace (Sym2 (boxVerts d N))))
  (hFKcovFam : ∀ (N : ℕ), 1 ≤ N → ∀ p ∈ Icc a b, HasDerivAt (fun p => fkProbOf (boxGraph d N) p 2 (Across N)) (deriv (fun p => fkProbOf (boxGraph d N) p 2 (Across N)) p) p ∧ ((N : ℝ) * c₀ * (fkProbOf (boxGraph d N) p 2 (Across N) * (1 - fkProbOf (boxGraph d N) p 2 (Across N))) ≤ D * ∑ e ∈ (boxGraph d N).edgeFinset, fkCov (boxGraph d N) p 2 ((Across N).indicator (fun _ => (1 : ℝ))) (coord e)) ∧ fkProbOf (boxGraph d N) p 2 (Across N) ≤ 1 - κ)
  (hBridge : ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 → (∀ N : ℕ, 1 ≤ N → fkProbOf (boxGraph d N) a 2 (Across N) ≤ Real.exp (-(4 * (N : ℝ) * c₀ * κ / D * (b - a)))) → FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0) :
-- imply
  ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 → FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0 := by
-- proof
  apply StatMech.FK.fkTheta_subcritical_eq_zero G d c₀ D κ hc₀ hD hκ a b hab ha0 hb1 Across hFKcovFam hBridge


-- created on 2026-10-23

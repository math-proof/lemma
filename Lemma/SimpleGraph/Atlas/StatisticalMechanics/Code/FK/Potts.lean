import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.Potts
open StatMech StatMech.Potts


/--
[monoIndicator_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Potts.lean)
-/
@[path]
private lemma monoIndicator_mk_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  {σ : V → Fin q}
  {x y : V} :
-- imply
  monoIndicator σ (s(x, y)) = if σ x = σ y then (1 : ℝ) else 0 := by
-- proof
  apply StatMech.Potts.monoIndicator_mk G σ x y

/--
[monoIndicator_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Potts.lean)
-/
@[path]
private lemma monoIndicator_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  {σ : V → Fin q}
  {e : Sym2 V} :
-- imply
  0 ≤ monoIndicator σ e := by
-- proof
  apply StatMech.Potts.monoIndicator_nonneg G σ e

/--
[agreement_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Potts.lean)
-/
@[path]
private lemma agreement_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  {σ : V → Fin q} :
-- imply
  0 ≤ agreement G σ := by
-- proof
  apply StatMech.Potts.agreement_nonneg G σ

/--
[pottsWeight_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Potts.lean)
-/
@[path]
private lemma pottsWeight_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  {β J : ℝ}
  {σ : V → Fin q} :
-- imply
  0 < pottsWeight G β J σ := by
-- proof
  apply StatMech.Potts.pottsWeight_pos G β J σ

/--
[pottsWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Potts.lean)
-/
@[path]
private lemma pottsWeight_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  {β J : ℝ}
  {σ : V → Fin q} :
-- imply
  0 ≤ pottsWeight G β J σ := by
-- proof
  apply StatMech.Potts.pottsWeight_nonneg G β J σ

/--
[pottsZ_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Potts.lean)
-/
@[path]
private lemma pottsZ_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  [NeZero q]
  {β J : ℝ} :
-- imply
  0 < pottsZ G q β J := by
-- proof
  apply StatMech.Potts.pottsZ_pos G q β J

/--
[pottsZ_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Potts.lean)
-/
@[path]
private lemma pottsZ_ne_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  [NeZero q]
  {β J : ℝ} :
-- imply
  pottsZ G q β J ≠ 0 := by
-- proof
  apply StatMech.Potts.pottsZ_ne_zero G q β J

/--
[pottsProb_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Potts.lean)
-/
@[path]
private lemma pottsProb_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  [NeZero q]
  {β J : ℝ}
  {σ : V → Fin q} :
-- imply
  0 ≤ pottsProb G q β J σ := by
-- proof
  apply StatMech.Potts.pottsProb_nonneg G q β J σ

/--
[pottsProb_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Potts.lean)
-/
@[path]
private lemma pottsProb_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  [NeZero q]
  {β J : ℝ}
  {σ : V → Fin q} :
-- imply
  0 < pottsProb G q β J σ := by
-- proof
  apply StatMech.Potts.pottsProb_pos G q β J σ

/--
[pottsProb_sum_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Potts.lean)
-/
@[path]
private lemma pottsProb_sum_eq_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  [NeZero q]
  {β J : ℝ} :
-- imply
  ∑ σ : V → Fin q, pottsProb G q β J σ = 1 := by
-- proof
  apply StatMech.Potts.pottsProb_sum_eq_one G q β J

/--
[pottsPMF_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Potts.lean)
-/
@[path]
private lemma pottsPMF_apply_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  [NeZero q]
  {β J : ℝ}
  {σ : V → Fin q} :
-- imply
  pottsPMF G q β J σ = ENNReal.ofReal (pottsProb G q β J σ) := by
-- proof
  apply StatMech.Potts.pottsPMF_apply G q β J σ


-- created on 2026-10-23

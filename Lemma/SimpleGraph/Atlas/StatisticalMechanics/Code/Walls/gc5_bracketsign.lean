import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc5_bracketsign
open Finset Classical StatMech StatMech.Walls


/--
[gc5_dep_ursell_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_bracketsign.lean)
-/
@[path]
private lemma gc5_dep_ursell_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Current V)}
  {B : Finset V}
  {o x y : V}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  egh_ensembleUrsell G β J M B o x y = -2 * tcp_allConnMass G β J M B o x y := by
-- proof
  apply StatMech.Walls.gc5_dep_ursell_eq G β J M B hox hoy hxy

/--
[gc5_dep_prob_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_bracketsign.lean)
-/
@[path]
private lemma gc5_dep_prob_le_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Current V)}
  {B : Finset V}
  {o x y : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  tcp_allConnProb G β J M B o x y ≤ 1 := by
-- proof
  apply StatMech.Walls.gc5_dep_prob_le_one G β J hβ hJ M B o x y

/--
[gc5_allConnMass_le_partition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_bracketsign.lean)
-/
@[path]
private lemma gc5_allConnMass_le_partition_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Current V)}
  {B : Finset V}
  {o x y : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  tcp_allConnMass G β J M B o x y ≤ tcp_partitionFunction G β J M B := by
-- proof
  apply StatMech.Walls.gc5_allConnMass_le_partition G β J hβ hJ M B o x y

/--
[gc5_bracket_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_bracketsign.lean)
-/
@[path]
private lemma gc5_bracket_nonpos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {μ P : ℝ}
-- given
  (hμ : 0 ≤ μ)
  (hP : 0 ≤ P) :
-- imply
  gc5_bracket μ P ≤ 0 := by
-- proof
  apply StatMech.Walls.gc5_bracket_nonpos G hμ hP

/--
[gc5_bracket_ge_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_bracketsign.lean)
-/
@[path]
private lemma gc5_bracket_ge_neg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {μ : ℝ}
  {P : ℝ}
-- given
  (hμ : 0 ≤ μ)
  (hP : P ≤ 1) :
-- imply
  -2 * μ ≤ gc5_bracket μ P := by
-- proof
  apply StatMech.Walls.gc5_bracket_ge_neg G μ hμ hP

/--
[gc5_bracket_sign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_bracketsign.lean)
-/
@[path]
private lemma gc5_bracket_sign_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {μ P : ℝ}
-- given
  (hμ : 0 ≤ μ)
  (hP0 : 0 ≤ P)
  (hP1 : P ≤ 1) :
-- imply
  -2 * μ ≤ gc5_bracket μ P ∧ gc5_bracket μ P ≤ 0 := by
-- proof
  apply StatMech.Walls.gc5_bracket_sign G hμ hP0 hP1

/--
[gc5_bracket_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_bracketsign.lean)
-/
@[path]
private lemma gc5_bracket_abs_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {μ P : ℝ}
-- given
  (hμ : 0 ≤ μ)
  (hP0 : 0 ≤ P)
  (hP1 : P ≤ 1) :
-- imply
  |gc5_bracket μ P| ≤ 2 * μ := by
-- proof
  apply StatMech.Walls.gc5_bracket_abs_le G hμ hP0 hP1

/--
[gc5_prob_mem_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_bracketsign.lean)
-/
@[path]
private lemma gc5_prob_mem_Icc_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Current V)}
  {B : Finset V}
  {o x y : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ tcp_allConnProb G β J M B o x y ∧ tcp_allConnProb G β J M B o x y ≤ 1 := by
-- proof
  apply StatMech.Walls.gc5_prob_mem_Icc G β J hβ hJ M B o x y

/--
[gc5_bracket_sign_ensemble](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_bracketsign.lean)
-/
@[path]
private lemma gc5_bracket_sign_ensemble_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Current V)}
  {B : Finset V}
  {o x y : V}
  {μ : ℝ}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hμ : 0 ≤ μ) :
-- imply
  -2 * μ ≤ gc5_bracket μ (tcp_allConnProb G β J M B o x y) ∧ gc5_bracket μ (tcp_allConnProb G β J M B o x y) ≤ 0 := by
-- proof
  apply StatMech.Walls.gc5_bracket_sign_ensemble G β J hβ hJ M B o x y hμ

/--
[gc5_bracket_eq_headline](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_bracketsign.lean)
-/
@[path]
private lemma gc5_bracket_eq_headline_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Current V)}
  {B : Finset V}
  {o x y : V}
  {μ : ℝ} :
-- imply
  gc5_bracket μ (tcp_allConnProb G β J M B o x y) = -2 * μ * tcp_allConnProb G β J M B o x y := by
-- proof
  apply StatMech.Walls.gc5_bracket_eq_headline G β J M B o x y μ

/--
[gc5_bracket_at_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_bracketsign.lean)
-/
@[path]
private lemma gc5_bracket_at_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {μ : ℝ} :
-- imply
  gc5_bracket μ 1 = -2 * μ := by
-- proof
  apply StatMech.Walls.gc5_bracket_at_one G μ

/--
[gc5_bracket_at_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_bracketsign.lean)
-/
@[path]
private lemma gc5_bracket_at_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {μ : ℝ} :
-- imply
  gc5_bracket μ 0 = 0 := by
-- proof
  apply StatMech.Walls.gc5_bracket_at_zero G μ

/--
[gc5_bracket_free_range](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_bracketsign.lean)
-/
@[path]
private lemma gc5_bracket_free_range_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {μ t : ℝ}
-- given
  (hμ : 0 ≤ μ)
  (hlo : -2 * μ ≤ t)
  (hhi : t ≤ 0) :
-- imply
  ∃ P : ℝ, 0 ≤ P ∧ P ≤ 1 ∧ gc5_bracket μ P = t := by
-- proof
  apply StatMech.Walls.gc5_bracket_free_range G hμ hlo hhi

/--
[gc5_bracket_sign_at_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_bracketsign.lean)
-/
@[path]
private lemma gc5_bracket_sign_at_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {μ : ℝ}
-- given
  (hμ : 0 ≤ μ) :
-- imply
  -2 * μ ≤ gc5_bracket μ 0 ∧ gc5_bracket μ 0 ≤ 0 := by
-- proof
  apply StatMech.Walls.gc5_bracket_sign_at_zero G hμ

/--
[gc5_bracket_sign_at_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_bracketsign.lean)
-/
@[path]
private lemma gc5_bracket_sign_at_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {μ : ℝ}
-- given
  (hμ : 0 ≤ μ) :
-- imply
  -2 * μ ≤ gc5_bracket μ 1 ∧ gc5_bracket μ 1 ≤ 0 := by
-- proof
  apply StatMech.Walls.gc5_bracket_sign_at_one G hμ


-- created on 2026-10-23

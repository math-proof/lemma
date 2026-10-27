import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc5_ensembleprob
open Finset BigOperators SimpleGraph Set StatMech StatMech.Walls


/--
[gc5_partitionFunction_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_ensembleprob.lean)
-/
@[path]
private lemma gc5_partitionFunction_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Ising.Current V)}
  {B : Finset V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ tcp_partitionFunction G β J M B := by
-- proof
  apply StatMech.Walls.gc5_partitionFunction_nonneg G β J hβ hJ M B

/--
[gc5_allConnMass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_ensembleprob.lean)
-/
@[path]
private lemma gc5_allConnMass_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Ising.Current V)}
  {B : Finset V}
  {o x y : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ tcp_allConnMass G β J M B o x y := by
-- proof
  apply StatMech.Walls.gc5_allConnMass_nonneg G β J hβ hJ M B o x y

/--
[gc5_allConnMass_le_partitionFunction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_ensembleprob.lean)
-/
@[path]
private lemma gc5_allConnMass_le_partitionFunction_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Ising.Current V)}
  {B : Finset V}
  {o x y : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  tcp_allConnMass G β J M B o x y ≤ tcp_partitionFunction G β J M B := by
-- proof
  apply StatMech.Walls.gc5_allConnMass_le_partitionFunction G β J hβ hJ M B o x y

/--
[gc5_ensemble_domination](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_ensembleprob.lean)
-/
@[path]
private lemma gc5_ensemble_domination_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Ising.Current V)}
  {B : Finset V}
  {o x y : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  2 * tcp_allConnMass G β J M B o x y ≤ tcp_partitionFunction G β J M B + tcp_allConnMass G β J M B o x y := by
-- proof
  apply StatMech.Walls.gc5_ensemble_domination G β J hβ hJ M B o x y

/--
[gc5_allConnProb_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_ensembleprob.lean)
-/
@[path]
private lemma gc5_allConnProb_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Ising.Current V)}
  {B : Finset V}
  {o x y : V} :
-- imply
  tcp_allConnProb G β J M B o x y = tcp_allConnMass G β J M B o x y / tcp_partitionFunction G β J M B := by
-- proof
  apply StatMech.Walls.gc5_allConnProb_eq G β J M B o x y

/--
[gc5_allConnProb_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_ensembleprob.lean)
-/
@[path]
private lemma gc5_allConnProb_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Ising.Current V)}
  {B : Finset V}
  {o x y : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ tcp_allConnProb G β J M B o x y := by
-- proof
  apply StatMech.Walls.gc5_allConnProb_nonneg G β J hβ hJ M B o x y

/--
[gc5_allConnProb_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_ensembleprob.lean)
-/
@[path]
private lemma gc5_allConnProb_le_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Ising.Current V)}
  {B : Finset V}
  {o x y : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  tcp_allConnProb G β J M B o x y ≤ 1 := by
-- proof
  apply StatMech.Walls.gc5_allConnProb_le_one G β J hβ hJ M B o x y

/--
[gc5_allConnProb_mem_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_ensembleprob.lean)
-/
@[path]
private lemma gc5_allConnProb_mem_Icc_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Ising.Current V)}
  {B : Finset V}
  {o x y : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  tcp_allConnProb G β J M B o x y ∈ Set.Icc (0 : ℝ) 1 := by
-- proof
  apply StatMech.Walls.gc5_allConnProb_mem_Icc G β J hβ hJ M B o x y

/--
[gc5_lebowitz_closes_U4](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_ensembleprob.lean)
-/
@[path]
private lemma gc5_lebowitz_closes_U4_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Ising.Current V)}
  {B : Finset V}
  {o x y : V}
  {μ : ℝ}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hμ : 0 ≤ μ) :
-- imply
  -2 * μ ≤ -2 * μ * tcp_allConnProb G β J M B o x y ∧ -2 * μ * tcp_allConnProb G β J M B o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc5_lebowitz_closes_U4 G β J hβ hJ M B o x y μ hμ

/--
[gc5_u3_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_ensembleprob.lean)
-/
@[path]
private lemma gc5_u3_nonpos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Ising.Current V)}
  {B : Finset V}
  {o x y : V}
  {μ : ℝ}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hμ : 0 ≤ μ) :
-- imply
  -2 * μ * tcp_allConnProb G β J M B o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc5_u3_nonpos G β J hβ hJ M B o x y μ hμ


-- created on 2026-10-23

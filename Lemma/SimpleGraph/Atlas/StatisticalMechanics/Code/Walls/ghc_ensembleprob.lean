import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.ghc_ensembleprob
open Finset Classical StatMech StatMech.Walls


/--
[ghc_allConnMass_le_partitionFunction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_ensembleprob.lean)
-/
@[path]
private lemma ghc_allConnMass_le_partitionFunction_eq
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
  apply StatMech.Walls.ghc_allConnMass_le_partitionFunction G β J hβ hJ M B o x y

/--
[ghc_allConnProb_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_ensembleprob.lean)
-/
@[path]
private lemma ghc_allConnProb_nonneg_eq
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
  apply StatMech.Walls.ghc_allConnProb_nonneg G β J hβ hJ M B o x y

/--
[ghc_allConnProb_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_ensembleprob.lean)
-/
@[path]
private lemma ghc_allConnProb_le_one_eq
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
  apply StatMech.Walls.ghc_allConnProb_le_one G β J hβ hJ M B o x y

/--
[ghc_allConnProb_mem_unitInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_ensembleprob.lean)
-/
@[path]
private lemma ghc_allConnProb_mem_unitInterval_eq
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
  0 ≤ tcp_allConnProb G β J M B o x y ∧ tcp_allConnProb G β J M B o x y ≤ 1 := by
-- proof
  apply StatMech.Walls.ghc_allConnProb_mem_unitInterval G β J hβ hJ M B o x y

/--
[ghc_allConnProb_mem_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_ensembleprob.lean)
-/
@[path]
private lemma ghc_allConnProb_mem_Icc_eq
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
  apply StatMech.Walls.ghc_allConnProb_mem_Icc G β J hβ hJ M B o x y


-- created on 2026-10-23

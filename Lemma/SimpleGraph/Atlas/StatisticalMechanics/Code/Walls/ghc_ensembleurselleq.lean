import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.ghc_ensembleurselleq
open Finset Classical StatMech StatMech.Walls


/--
[ghc_switching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_ensembleurselleq.lean)
-/
@[path]
private lemma ghc_switching_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : Current V}
  {u v : V}
  {A : Finset V}
-- given
  (huv : u ≠ v)
  (hconn : connP (oddEdges G.edgeFinset m) u v) :
-- imply
  hnw_mass G β J m (A ∆ {u, v}) = hnw_mass G β J m A := by
-- proof
  apply StatMech.Walls.ghc_switching G β J m huv hconn A

/--
[ghc_gap_allConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_ensembleurselleq.lean)
-/
@[path]
private lemma ghc_gap_allConn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : Current V}
  {A : Finset V}
  {o x y : V}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hall : hnw_allConn G m o x y) :
-- imply
  hnw_gap G β J m A o x y = -2 * hnw_mass G β J m A := by
-- proof
  apply StatMech.Walls.ghc_gap_allConn G β J m A hox hoy hxy hall

/--
[ghc_ensemble_ursell_eq_unfolded](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_ensembleurselleq.lean)
-/
@[path]
private lemma ghc_ensemble_ursell_eq_unfolded_eq
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
  ∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_gap G β J m B o x y = -2 * ∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m B := by
-- proof
  apply StatMech.Walls.ghc_ensemble_ursell_eq_unfolded G β J M B hox hoy hxy

/--
[ghc_ensemble_ursell_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_ensembleurselleq.lean)
-/
@[path]
private lemma ghc_ensemble_ursell_eq_eq
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
  ghc_ensembleUrsell G β J M B o x y = -2 * ghc_allConnMass G β J M B o x y := by
-- proof
  apply StatMech.Walls.ghc_ensemble_ursell_eq G β J M B hox hoy hxy

/--
[ghc_ensembleUrsell_eq_egh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_ensembleurselleq.lean)
-/
@[path]
private lemma ghc_ensembleUrsell_eq_egh_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Current V)}
  {B : Finset V}
  {o x y : V} :
-- imply
  ghc_ensembleUrsell G β J M B o x y = egh_ensembleUrsell G β J M B o x y := by
-- proof
  apply StatMech.Walls.ghc_ensembleUrsell_eq_egh G β J M B o x y

/--
[ghc_allConnMass_eq_tcp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_ensembleurselleq.lean)
-/
@[path]
private lemma ghc_allConnMass_eq_tcp_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Current V)}
  {B : Finset V}
  {o x y : V} :
-- imply
  ghc_allConnMass G β J M B o x y = tcp_allConnMass G β J M B o x y := by
-- proof
  apply StatMech.Walls.ghc_allConnMass_eq_tcp G β J M B o x y


-- created on 2026-10-23

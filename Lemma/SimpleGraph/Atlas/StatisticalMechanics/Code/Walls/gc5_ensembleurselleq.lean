import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc5_ensembleurselleq
open Finset BigOperators SimpleGraph Set Classical StatMech StatMech.Walls


/--
[gc5_ensembleUrsell_eq_egh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_ensembleurselleq.lean)
-/
@[path]
private lemma gc5_ensembleUrsell_eq_egh_eq
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
  gc5_ensembleUrsell G β J M B o x y = egh_ensembleUrsell G β J M B o x y := by
-- proof
  apply StatMech.Walls.gc5_ensembleUrsell_eq_egh G β J M B o x y

/--
[gc5_three_pairings_collapse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_ensembleurselleq.lean)
-/
@[path]
private lemma gc5_three_pairings_collapse_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : Current V}
  {B : Finset V}
  {o x y : V}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hall : hnw_allConn G m o x y) :
-- imply
  hnw_mass G β J m (B ∆ {x, y}) = hnw_mass G β J m B ∧ hnw_mass G β J m (B ∆ {o, y}) = hnw_mass G β J m B ∧ hnw_mass G β J m (B ∆ {o, x}) = hnw_mass G β J m B := by
-- proof
  apply StatMech.Walls.gc5_three_pairings_collapse G β J m B hox hoy hxy hall

/--
[gc5_gap_allConn_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_ensembleurselleq.lean)
-/
@[path]
private lemma gc5_gap_allConn_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : Current V}
  {B : Finset V}
  {o x y : V}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hall : hnw_allConn G m o x y) :
-- imply
  hnw_gap G β J m B o x y = -2 * hnw_mass G β J m B := by
-- proof
  apply StatMech.Walls.gc5_gap_allConn_eq G β J m B hox hoy hxy hall

/--
[gc5_ensemble_ursell_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_ensembleurselleq.lean)
-/
@[path]
private lemma gc5_ensemble_ursell_eq_eq
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
  gc5_ensembleUrsell G β J M B o x y = -2 * tcp_allConnMass G β J M B o x y := by
-- proof
  apply StatMech.Walls.gc5_ensemble_ursell_eq G β J M B hox hoy hxy

/--
[gc5_ensembleUrsell_eq_neg_two_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_ensembleurselleq.lean)
-/
@[path]
private lemma gc5_ensembleUrsell_eq_neg_two_mul_eq
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
  (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_gap G β J m B o x y) = -2 * (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m B) := by
-- proof
  apply StatMech.Walls.gc5_ensembleUrsell_eq_neg_two_mul G β J M B hox hoy hxy

/--
[gc5_ensemble_ursell_eq_agrees](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_ensembleurselleq.lean)
-/
@[path]
private lemma gc5_ensemble_ursell_eq_agrees_eq
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
  gc5_ensembleUrsell G β J M B o x y = egh_ensembleUrsell G β J M B o x y ∧ gc5_ensembleUrsell G β J M B o x y = -2 * tcp_allConnMass G β J M B o x y := by
-- proof
  apply StatMech.Walls.gc5_ensemble_ursell_eq_agrees G β J M B hox hoy hxy

/--
[gc5_ensemble_ursell_sign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_ensembleurselleq.lean)
-/
@[path]
private lemma gc5_ensemble_ursell_sign_eq
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
  (hJ : ∀ e, 0 ≤ J e)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  gc5_ensembleUrsell G β J M B o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc5_ensemble_ursell_sign G β J hβ hJ M B hox hoy hxy

/--
[gc5_ursell_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_ensembleurselleq.lean)
-/
@[path]
private lemma gc5_ursell_empty_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {B : Finset V}
  {o x y : V} :
-- imply
  gc5_ensembleUrsell G β J (∅ : Finset (Current V)) B o x y = 0 := by
-- proof
  apply StatMech.Walls.gc5_ursell_empty G β J B o x y

/--
[gc5_ursell_single_allConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_ensembleurselleq.lean)
-/
@[path]
private lemma gc5_ursell_single_allConn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : Current V}
  {B : Finset V}
  {o x y : V}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hall : hnw_allConn G m o x y) :
-- imply
  gc5_ensembleUrsell G β J ({m} : Finset (Current V)) B o x y = -2 * hnw_mass G β J m B := by
-- proof
  apply StatMech.Walls.gc5_ursell_single_allConn G β J m B hox hoy hxy hall

/--
[gc5_ursell_single_noneConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_ensembleurselleq.lean)
-/
@[path]
private lemma gc5_ursell_single_noneConn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : Current V}
  {B : Finset V}
  {o x y : V}
-- given
  (hnall : ¬ hnw_allConn G m o x y) :
-- imply
  gc5_ensembleUrsell G β J ({m} : Finset (Current V)) B o x y = 0 := by
-- proof
  apply StatMech.Walls.gc5_ursell_single_noneConn G β J m B o x y hnall


-- created on 2026-10-23

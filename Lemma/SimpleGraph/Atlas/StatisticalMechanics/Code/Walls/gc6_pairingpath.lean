import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc6_pairingpath
open Finset BigOperators StatMech StatMech.Walls


/--
[gc6_adjStep_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc6_pairingpath.lean)
-/
@[path]
private lemma gc6_adjStep_mono_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {ends : ι → Sym2 V}
  {N m : Finset ι}
  {a b : V}
-- given
  (hNm : N ⊆ m)
  (h : adjStep ends N a b) :
-- imply
  adjStep ends m a b := by
-- proof
  apply StatMech.Walls.gc6_adjStep_mono G ends hNm h

/--
[gc6_connK_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc6_pairingpath.lean)
-/
@[path]
private lemma gc6_connK_mono_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {ends : ι → Sym2 V}
  {N m : Finset ι}
  {i j : V}
-- given
  (hNm : N ⊆ m)
  (h : connK ends N i j) :
-- imply
  connK ends m i j := by
-- proof
  apply StatMech.Walls.gc6_connK_mono G ends hNm h

/--
[gc6_pairingPath_abstract](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc6_pairingpath.lean)
-/
@[path]
private lemma gc6_pairingPath_abstract_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq ι]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {N m : Finset ι}
  {i j : V}
-- given
  (hnd : ∀ i ∈ N, ¬ (ends i).IsDiag)
  (hNm : N ⊆ m)
  (hbdry : sources ends N = {i, j})
  (hij : i ≠ j) :
-- imply
  connK ends m i j := by
-- proof
  apply StatMech.Walls.gc6_pairingPath_abstract G ends N m hnd hNm hbdry hij

/--
[gc6_pairingPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc6_pairingpath.lean)
-/
@[path]
private lemma gc6_pairingPath_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {N : Finset (Copy G m)}
  {i j : V}
-- given
  (hbdry : sources (endsM G m) N = {i, j})
  (hij : i ≠ j) :
-- imply
  connK (endsM G m) (univ : Finset (Copy G m)) i j := by
-- proof
  apply StatMech.Walls.gc6_pairingPath G m N hbdry hij

/--
[gc6_pairingPath_currentConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc6_pairingpath.lean)
-/
@[path]
private lemma gc6_pairingPath_currentConnected_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {N : Finset (Copy G m)}
  {i j : V}
-- given
  (hbdry : sources (endsM G m) N = {i, j})
  (hij : i ≠ j) :
-- imply
  CurrentConnected G (ofEdgeFun G (profileFlux G m (univ : Finset (Copy G m)))) i j := by
-- proof
  apply StatMech.Walls.gc6_pairingPath_currentConnected G m N hbdry hij

/--
[gc6_pairingPath_oddDegree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc6_pairingpath.lean)
-/
@[path]
private lemma gc6_pairingPath_oddDegree_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {N : Finset (Copy G m)}
  {i j : V}
-- given
  (hi_odd : Odd (degK (endsM G m) N i))
  (hj_odd : Odd (degK (endsM G m) N j))
  (hother : ∀ x, Odd (degK (endsM G m) N x) → x = i ∨ x = j)
  (hij : i ≠ j) :
-- imply
  connK (endsM G m) (univ : Finset (Copy G m)) i j := by
-- proof
  apply StatMech.Walls.gc6_pairingPath_oddDegree G m N hi_odd hj_odd hother hij


-- created on 2026-10-23

import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc2_componenthandshake
open Finset BigOperators StatMech StatMech.Walls


/--
[gc2_componentHandshake_abstract](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc2_componenthandshake.lean)
-/
@[path]
private lemma gc2_componentHandshake_abstract_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq ι]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {M : Finset ι}
  {u v : V}
-- given
  (hnd : ∀ i ∈ M, ¬ (ends i).IsDiag)
  (hu_odd : Odd (degK ends M u))
  (hbdry : ∀ x, Odd (degK ends M x) → x = u ∨ x = v)
  (huv : u ≠ v) :
-- imply
  connK ends M u v := by
-- proof
  apply StatMech.Walls.gc2_componentHandshake_abstract G ends M hnd hu_odd hbdry huv

/--
[gc2_componentHandshake](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc2_componenthandshake.lean)
-/
@[path]
private lemma gc2_componentHandshake_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {M : Finset (Copy G m)}
  {u v : V}
-- given
  (hu_odd : Odd (degK (endsM G m) M u))
  (hbdry : ∀ x, Odd (degK (endsM G m) M x) → x = u ∨ x = v)
  (huv : u ≠ v) :
-- imply
  connK (endsM G m) M u v := by
-- proof
  apply StatMech.Walls.gc2_componentHandshake G m M hu_odd hbdry huv

/--
[gc2_componentHandshake_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc2_componenthandshake.lean)
-/
@[path]
private lemma gc2_componentHandshake_sources_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {M : Finset (Copy G m)}
  {u v : V}
-- given
  (hbdry : RandomCurrent.sources (endsM G m) M = {u, v})
  (huv : u ≠ v) :
-- imply
  connK (endsM G m) M u v := by
-- proof
  apply StatMech.Walls.gc2_componentHandshake_sources G m M hbdry huv

/--
[gc2_componentHandshake_mem_compOf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc2_componenthandshake.lean)
-/
@[path]
private lemma gc2_componentHandshake_mem_compOf_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {M : Finset (Copy G m)}
  {u v : V}
-- given
  (hbdry : RandomCurrent.sources (endsM G m) M = {u, v})
  (huv : u ≠ v) :
-- imply
  v ∈ compOf (endsM G m) M u := by
-- proof
  apply StatMech.Walls.gc2_componentHandshake_mem_compOf G m M hbdry huv

/--
[gc2_componentHandshake_oddComp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc2_componenthandshake.lean)
-/
@[path]
private lemma gc2_componentHandshake_oddComp_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {M : Finset (Copy G m)}
  {u v : V}
-- given
  (hbdry : RandomCurrent.sources (endsM G m) M = {u, v})
  (huv : u ≠ v) :
-- imply
  (compOf (endsM G m) M u).filter (fun x => Odd (degK (endsM G m) M x)) = {u, v} := by
-- proof
  apply StatMech.Walls.gc2_componentHandshake_oddComp G m M hbdry huv


-- created on 2026-10-23

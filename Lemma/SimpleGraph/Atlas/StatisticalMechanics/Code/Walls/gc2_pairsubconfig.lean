import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gc2_pairsubconfig
open Finset BigOperators Classical StatMech StatMech.Walls


/--
[gc2_walk_subconfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc2_pairsubconfig.lean)
-/
@[path]
private lemma gc2_walk_subconfig_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {u : V} :
-- imply
  ∀ {w : V}, connK ends m u w → ∃ P ⊆ m, sources ends P = ({u} : Finset V) ∆ {w} := by
-- proof
  apply StatMech.Walls.gc2_walk_subconfig ends m u

/--
[gc2_singleton_symmDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc2_pairsubconfig.lean)
-/
@[path]
private lemma gc2_singleton_symmDiff_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {u v : V}
-- given
  (huv : u ≠ v) :
-- imply
  ({u} : Finset V) ∆ {v} = {u, v} := by
-- proof
  apply StatMech.Walls.gc2_singleton_symmDiff huv

/--
[gc2_pair_subconfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc2_pairsubconfig.lean)
-/
@[path]
private lemma gc2_pair_subconfig_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {u v : V}
-- given
  (hconn : connK ends m u v)
  (huv : u ≠ v) :
-- imply
  ∃ P ⊆ m, sources ends P = {u, v} := by
-- proof
  apply StatMech.Walls.gc2_pair_subconfig ends m hconn huv

/--
[gc2_pair_subconfig_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc2_pairsubconfig.lean)
-/
@[path]
private lemma gc2_pair_subconfig_exists_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {u v : V}
-- given
  (hconn : connK ends m u v)
  (huv : u ≠ v) :
-- imply
  ∃ P : Finset ι, P ⊆ m ∧ sources ends P = {u, v} := by
-- proof
  apply StatMech.Walls.gc2_pair_subconfig_exists ends m hconn huv

/--
[gc2_pair_subconfig_eq_exists_conn_set](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc2_pairsubconfig.lean)
-/
@[path]
private lemma gc2_pair_subconfig_eq_exists_conn_set_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {u v : V}
-- given
  (hconn : connK ends m u v)
  (huv : u ≠ v) :
-- imply
  (∃ P ⊆ m, sources ends P = ({u, v} : Finset V)) ↔ (∃ P ⊆ m, sources ends P = ({u, v} : Finset V)) := by
-- proof
  apply StatMech.Walls.gc2_pair_subconfig_eq_exists_conn_set ends m hconn huv


-- created on 2026-10-23

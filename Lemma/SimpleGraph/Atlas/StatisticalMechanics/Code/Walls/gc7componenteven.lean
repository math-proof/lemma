import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
open Finset BigOperators StatMech StatMech.Walls


/--
[gc7_componentEven_abstract](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc7componenteven.lean)
-/
@[path]
private lemma gc7_componentEven_abstract_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq ι]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {M : Finset ι}
  {u : V}
-- given
  (hnd : ∀ i ∈ M, ¬ (ends i).IsDiag) :
-- imply
  Even (#((compOf ends M u).filter (fun x => Odd (degK ends M x)))) := by
-- proof
  apply StatMech.Walls.gc7_componentEven_abstract G ends M hnd u

/--
[gc7_oddComp_eq_sources_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc7componenteven.lean)
-/
@[path]
private lemma gc7_oddComp_eq_sources_inter_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq ι]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {M : Finset ι}
  {u : V} :
-- imply
  (compOf ends M u).filter (fun x => Odd (degK ends M x)) = (sources ends M) ∩ (compOf ends M u) := by
-- proof
  apply StatMech.Walls.gc7_oddComp_eq_sources_inter G ends M u

/--
[gc7_componentEven_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc7componenteven.lean)
-/
@[path]
private lemma gc7_componentEven_sources_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq ι]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {M : Finset ι}
  {u : V}
-- given
  (hnd : ∀ i ∈ M, ¬ (ends i).IsDiag) :
-- imply
  Even (#((sources ends M) ∩ (compOf ends M u))) := by
-- proof
  apply StatMech.Walls.gc7_componentEven_sources G ends M hnd u

/--
[gc7_componentEven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc7componenteven.lean)
-/
@[path]
private lemma gc7_componentEven_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {M : Finset (Copy G m)}
  {u : V} :
-- imply
  Even (#((compOf (endsM G m) M u).filter (fun x => Odd (degK (endsM G m) M x)))) := by
-- proof
  apply StatMech.Walls.gc7_componentEven G m M u

/--
[gc7_componentEven_sources_edgeCopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc7componenteven.lean)
-/
@[path]
private lemma gc7_componentEven_sources_edgeCopy_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {M : Finset (Copy G m)}
  {u : V} :
-- imply
  Even (#((sources (endsM G m) M) ∩ (compOf (endsM G m) M u))) := by
-- proof
  apply StatMech.Walls.gc7_componentEven_sources_edgeCopy G m M u

/--
[gc7_total_handshake](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc7componenteven.lean)
-/
@[path]
private lemma gc7_total_handshake_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq ι]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {M : Finset ι}
-- given
  (hnd : ∀ i ∈ M, ¬ (ends i).IsDiag) :
-- imply
  Even (#(sources ends M)) := by
-- proof
  apply StatMech.Walls.gc7_total_handshake G ends M hnd

/--
[gc7_total_handshake_edgeCopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc7componenteven.lean)
-/
@[path]
private lemma gc7_total_handshake_edgeCopy_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {M : Finset (Copy G m)} :
-- imply
  Even (#(sources (endsM G m) M)) := by
-- proof
  apply StatMech.Walls.gc7_total_handshake_edgeCopy G m M

/--
[gc7_componentEven_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc7componenteven.lean)
-/
@[path]
private lemma gc7_componentEven_pair_eq
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
  v ∈ compOf ends M u := by
-- proof
  apply StatMech.Walls.gc7_componentEven_pair G ends M hnd hu_odd hbdry huv


-- created on 2026-10-23

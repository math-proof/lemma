import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredEuler
open Finset StatMech StatMech.Universality


/--
[fkIsingSquareWired_completedLoop_componentCount_of_not_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredEuler.lean)
-/
@[path]
private lemma fkIsingSquareWired_completedLoop_componentCount_of_not_reachable_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hsep : ¬ (openSub (fkSquareBoxPlanar n).G (setClosed e.1 omega) ⊔ (fkIsingSquareWiredDobrushinDomain n hn).wiring).Reachable (fkIsingSquareOrientedEdge n e).tail (fkIsingSquareOrientedEdge n e).head) :
-- imply
  Nat.card (fkIsingSquareWiredCompletedLoopGraph n hn (setOpen e.1 omega)).ConnectedComponent + 1 = Nat.card (fkIsingSquareWiredCompletedLoopGraph n hn (setClosed e.1 omega)).ConnectedComponent := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_completedLoop_componentCount_of_not_reachable n hn omega e hsep

/--
[fkIsingSquareWiredEulerDefect_setOpen_eq_setClosed_of_not_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredEuler.lean)
-/
@[path]
private lemma fkIsingSquareWiredEulerDefect_setOpen_eq_setClosed_of_not_reachable_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hsep : ¬ (openSub (fkSquareBoxPlanar n).G (setClosed e.1 omega) ⊔ (fkIsingSquareWiredDobrushinDomain n hn).wiring).Reachable (fkIsingSquareOrientedEdge n e).tail (fkIsingSquareOrientedEdge n e).head) :
-- imply
  fkIsingSquareWiredEulerDefect n hn (setOpen e.1 omega) = fkIsingSquareWiredEulerDefect n hn (setClosed e.1 omega) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredEulerDefect_setOpen_eq_setClosed_of_not_reachable n hn omega e hsep

/--
[fkIsingSquareWiredEulerDefect_setClosed_le_setOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredEuler.lean)
-/
@[path]
private lemma fkIsingSquareWiredEulerDefect_setClosed_le_setOpen_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredEulerDefect n hn (setClosed e.1 omega) ≤ fkIsingSquareWiredEulerDefect n hn (setOpen e.1 omega) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredEulerDefect_setClosed_le_setOpen n hn omega e

/--
[fkIsingSquareWiredEulerDefect_congr_on_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredEuler.lean)
-/
@[path]
private lemma fkIsingSquareWiredEulerDefect_congr_on_edges_eq
  {n : Nat}
  {omega eta : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
-- given
  (hn : 0 < n)
  (hagree : ∀ f ∈ (fkSquareBoxPlanar n).G.edgeFinset, omega f = eta f) :
-- imply
  fkIsingSquareWiredEulerDefect n hn omega = fkIsingSquareWiredEulerDefect n hn eta := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredEulerDefect_congr_on_edges n hn omega eta hagree

/--
[fkIsingSquareWiredEulerDefect_eq_of_empty_full_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredEuler.lean)
-/
@[path]
private lemma fkIsingSquareWiredEulerDefect_eq_of_empty_full_eq_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
-- given
  (hn : 0 < n)
  (hends : fkIsingSquareWiredEulerDefect n hn (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset) = fkIsingSquareWiredEulerDefect n hn (FK.edgeSetConfig ∅)) :
-- imply
  fkIsingSquareWiredEulerDefect n hn omega = fkIsingSquareWiredEulerDefect n hn (FK.edgeSetConfig ∅) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredEulerDefect_eq_of_empty_full_eq n hn hends omega

/--
[fkIsingSquareWiredEulerDefect_toggle_eq_of_empty_full_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredEuler.lean)
-/
@[path]
private lemma fkIsingSquareWiredEulerDefect_toggle_eq_of_empty_full_eq_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hends : fkIsingSquareWiredEulerDefect n hn (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset) = fkIsingSquareWiredEulerDefect n hn (FK.edgeSetConfig ∅)) :
-- imply
  fkIsingSquareWiredEulerDefect n hn (setOpen e.1 omega) = fkIsingSquareWiredEulerDefect n hn (setClosed e.1 omega) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredEulerDefect_toggle_eq_of_empty_full_eq n hn hends omega e


-- created on 2026-10-23

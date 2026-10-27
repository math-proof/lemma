import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc10allconnforcing
open Finset BigOperators StatMech StatMech.Walls


/--
[gc10_allConn_pairwise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10allconnforcing.lean)
-/
@[path]
private lemma gc10_allConn_pairwise_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {ends : ι → Sym2 V}
  {o x y g : V}
  {m : Finset ι}
-- given
  (h : gc10_allConn ends o x y g m) :
-- imply
  connK ends m o x ∧ connK ends m o y ∧ connK ends m o g ∧ connK ends m x y ∧ connK ends m x g ∧ connK ends m y g := by
-- proof
  apply StatMech.Walls.gc10_allConn_pairwise ends o x y g m h

/--
[gc10_allConnForcing_disconnect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10allconnforcing.lean)
-/
@[path]
private lemma gc10_allConnForcing_disconnect_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y g : V}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (hsrc : sources ends m = {o, x, y, g})
  (hog_disc : ¬ connK ends m o g) :
-- imply
  ((connK ends m o x ∧ connK ends m y g) ∨ (connK ends m o y ∧ connK ends m x g)) ∧ ¬ ((connK ends m o x ∧ connK ends m y g) ∧ (connK ends m o y ∧ connK ends m x g)) := by
-- proof
  apply StatMech.Walls.gc10_allConnForcing_disconnect ends m hnd o x y g hox hoy hog hxy hxg hyg hsrc hog_disc

/--
[gc10_disconnect_iff_crossPairing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10allconnforcing.lean)
-/
@[path]
private lemma gc10_disconnect_iff_crossPairing_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y g : V}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (hsrc : sources ends m = {o, x, y, g}) :
-- imply
  (¬ connK ends m o g) ↔ (gc8_caseA ends o x y g m ∨ gc8_caseB ends o x y g m) := by
-- proof
  apply StatMech.Walls.gc10_disconnect_iff_crossPairing ends m hnd o x y g hox hoy hog hxy hxg hyg hsrc

/--
[gc10_crossPairing_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10allconnforcing.lean)
-/
@[path]
private lemma gc10_crossPairing_disjoint_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y g : V}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (hsrc : sources ends m = {o, x, y, g}) :
-- imply
  ¬ (gc8_caseA ends o x y g m ∧ gc8_caseB ends o x y g m) := by
-- proof
  apply StatMech.Walls.gc10_crossPairing_disjoint ends m hnd o x y g hox hoy hog hxy hxg hyg hsrc

/--
[gc10_allConn_of_no_crossPairing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10allconnforcing.lean)
-/
@[path]
private lemma gc10_allConn_of_no_crossPairing_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y g : V}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (hsrc : sources ends m = {o, x, y, g})
  (hnA : ¬ gc8_caseA ends o x y g m)
  (hnB : ¬ gc8_caseB ends o x y g m) :
-- imply
  connK ends m o g := by
-- proof
  apply StatMech.Walls.gc10_allConn_of_no_crossPairing ends m hnd o x y g hox hoy hog hxy hxg hyg hsrc hnA hnB

/--
[gc10_allConnected_forced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10allconnforcing.lean)
-/
@[path]
private lemma gc10_allConnected_forced_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {ends : ι → Sym2 V}
  {o x y g : V}
  {m : Finset ι}
-- given
  (hox : connK ends m o x)
  (hoy : connK ends m o y)
  (hog : connK ends m o g) :
-- imply
  gc10_allConn ends o x y g m := by
-- proof
  apply StatMech.Walls.gc10_allConnected_forced ends o x y g m hox hoy hog

/--
[gc10_allConnForcing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10allconnforcing.lean)
-/
@[path]
private lemma gc10_allConnForcing_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y g : V}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (hsrc : sources ends m = {o, x, y, g})
  (harcx : connK ends m o x)
  (harcy : connK ends m o y) :
-- imply
  ((connK ends m o g ∧ gc10_allConn ends o x y g m) ∨ gc8_caseA ends o x y g m ∨ gc8_caseB ends o x y g m) ∧ (connK ends m o g → ¬ gc8_caseA ends o x y g m) ∧ (connK ends m o g → ¬ gc8_caseB ends o x y g m) ∧ ¬ (gc8_caseA ends o x y g m ∧ gc8_caseB ends o x y g m) := by
-- proof
  apply StatMech.Walls.gc10_allConnForcing ends m hnd o x y g hox hoy hog hxy hxg hyg hsrc harcx harcy

/--
[gc10_crossing_forces_allConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10allconnforcing.lean)
-/
@[path]
private lemma gc10_crossing_forces_allConn_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {ends : ι → Sym2 V}
  {o x y g w : V}
  {m : Finset ι}
-- given
  (hox : connK ends m o x)
  (hyg : connK ends m y g)
  (hwo : connK ends m w o)
  (hwy : connK ends m w y) :
-- imply
  gc10_allConn ends o x y g m := by
-- proof
  apply StatMech.Walls.gc10_crossing_forces_allConn ends m hox hyg hwo hwy

/--
[gc10_crossPairing_not_implies_disconnect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10allconnforcing.lean)
-/
@[path]
private lemma gc10_crossPairing_not_implies_disconnect_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V] :
-- imply
  ∃ (ends : Fin 3 → Sym2 (Fin 4)) (m : Finset (Fin 3)), (connK ends m 0 1 ∧ connK ends m 2 3) ∧ connK ends m 0 3 := by
-- proof
  apply StatMech.Walls.gc10_crossPairing_not_implies_disconnect

/--
[gc10_allConnForcing_trichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10allconnforcing.lean)
-/
@[path]
private lemma gc10_allConnForcing_trichotomy_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y g : V}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (hsrc : sources ends m = {o, x, y, g}) :
-- imply
  (connK ends m o g) ∨ (connK ends m o x ∧ connK ends m y g) ∨ (connK ends m o y ∧ connK ends m x g) := by
-- proof
  apply StatMech.Walls.gc10_allConnForcing_trichotomy ends m hnd o x y g hox hoy hog hxy hxg hyg hsrc

/--
[gc10_allConnForcing_disconnect_edgeCopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10allconnforcing.lean)
-/
@[path]
private lemma gc10_allConnForcing_disconnect_edgeCopy_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {K : Finset (Copy G m)}
  {o x y g : W}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (hsrc : sources (endsM G m) K = ({o, x, y, g} : Finset W))
  (hog_disc : ¬ connK (endsM G m) K o g) :
-- imply
  ((connK (endsM G m) K o x ∧ connK (endsM G m) K y g) ∨ (connK (endsM G m) K o y ∧ connK (endsM G m) K x g)) ∧ ¬ ((connK (endsM G m) K o x ∧ connK (endsM G m) K y g) ∧ (connK (endsM G m) K o y ∧ connK (endsM G m) K x g)) := by
-- proof
  apply StatMech.Walls.gc10_allConnForcing_disconnect_edgeCopy G m K o x y g hox hoy hog hxy hxg hyg hsrc hog_disc

/--
[gc10_allConnForcing_trichotomy_edgeCopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10allconnforcing.lean)
-/
@[path]
private lemma gc10_allConnForcing_trichotomy_edgeCopy_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {K : Finset (Copy G m)}
  {o x y g : W}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (hsrc : sources (endsM G m) K = ({o, x, y, g} : Finset W)) :
-- imply
  (connK (endsM G m) K o g) ∨ (connK (endsM G m) K o x ∧ connK (endsM G m) K y g) ∨ (connK (endsM G m) K o y ∧ connK (endsM G m) K x g) := by
-- proof
  apply StatMech.Walls.gc10_allConnForcing_trichotomy_edgeCopy G m K o x y g hox hoy hog hxy hxg hyg hsrc

/--
[gc10_allConnected_forced_edgeCopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10allconnforcing.lean)
-/
@[path]
private lemma gc10_allConnected_forced_edgeCopy_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {K : Finset (Copy G m)}
  {o x y g : W}
-- given
  (hox : connK (endsM G m) K o x)
  (hoy : connK (endsM G m) K o y)
  (hog : connK (endsM G m) K o g) :
-- imply
  gc10_allConn (endsM G m) o x y g K := by
-- proof
  apply StatMech.Walls.gc10_allConnected_forced_edgeCopy G m K o x y g hox hoy hog

/--
[gc10_allConnForcing_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10allconnforcing.lean)
-/
@[path]
private lemma gc10_allConnForcing_nonvacuous_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype W]
  [DecidableEq W] :
-- imply
  let ends : Fin 2 → Sym2 (Fin 4) := fun i => if i = 0 then s(0, 1) else s(2, 3) sources ends (univ : Finset (Fin 2)) = ({0, 1, 2, 3} : Finset (Fin 4)) ∧ ¬ connK ends (univ : Finset (Fin 2)) 0 3 ∧ connK ends (univ : Finset (Fin 2)) 0 1 ∧ connK ends (univ : Finset (Fin 2)) 2 3 := by
-- proof
  apply StatMech.Walls.gc10_allConnForcing_nonvacuous


-- created on 2026-10-23

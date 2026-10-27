import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc7core
open Finset BigOperators StatMech StatMech.Walls


/--
[gc7_core_marks_in_cluster_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc7core.lean)
-/
@[path]
private lemma gc7_core_marks_in_cluster_even_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {ends : ι → Sym2 V}
  {K : Finset ι}
  {o x y g u : V}
-- given
  (hnd : ∀ i ∈ K, ¬ (ends i).IsDiag)
  (hbdry : sources ends K = ({o, x, y, g} : Finset V)) :
-- imply
  Even (#(({o, x, y, g} : Finset V) ∩ (compOf ends K u))) := by
-- proof
  apply StatMech.Walls.gc7_core_marks_in_cluster_even ends K hnd o x y g u hbdry

/--
[gc7_core_ox_xor_oy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc7core.lean)
-/
@[path]
private lemma gc7_core_ox_xor_oy_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {ends : ι → Sym2 V}
  {K : Finset ι}
  {o x y g : V}
-- given
  (hnd : ∀ i ∈ K, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (hbdry : sources ends K = ({o, x, y, g} : Finset V))
  (hog_disc : ¬ connK ends K o g) :
-- imply
  (connK ends K o x) ≠ (connK ends K o y) := by
-- proof
  apply StatMech.Walls.gc7_core_ox_xor_oy ends K hnd o x y g hox hoy hog hxy hxg hyg hbdry hog_disc

/--
[gc7_core_complementary_yg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc7core.lean)
-/
@[path]
private lemma gc7_core_complementary_yg_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {ends : ι → Sym2 V}
  {K : Finset ι}
  {o x y g : V}
-- given
  (hnd : ∀ i ∈ K, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (hbdry : sources ends K = ({o, x, y, g} : Finset V))
  (hoy_disc : ¬ connK ends K o y)
  (hox_conn : connK ends K o x) :
-- imply
  connK ends K y g := by
-- proof
  apply StatMech.Walls.gc7_core_complementary_yg ends K hnd o x y g hox hoy hog hxy hxg hyg hbdry hoy_disc hox_conn

/--
[gc7_core_complementary_xg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc7core.lean)
-/
@[path]
private lemma gc7_core_complementary_xg_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {ends : ι → Sym2 V}
  {K : Finset ι}
  {o x y g : V}
-- given
  (hnd : ∀ i ∈ K, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (hbdry : sources ends K = ({o, x, y, g} : Finset V))
  (hox_disc : ¬ connK ends K o x)
  (hoy_conn : connK ends K o y) :
-- imply
  connK ends K x g := by
-- proof
  apply StatMech.Walls.gc7_core_complementary_xg ends K hnd o x y g hox hoy hog hxy hxg hyg hbdry hox_disc hoy_conn

/--
[gc7_core_pathCrossing_dichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc7core.lean)
-/
@[path]
private lemma gc7_core_pathCrossing_dichotomy_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {ends : ι → Sym2 V}
  {K : Finset ι}
  {o x y g : V}
-- given
  (hnd : ∀ i ∈ K, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (hbdry : sources ends K = ({o, x, y, g} : Finset V))
  (hog_disc : ¬ connK ends K o g) :
-- imply
  ((connK ends K o x ∧ connK ends K y g) ∨ (connK ends K o y ∧ connK ends K x g)) ∧ ¬ ((connK ends K o x ∧ connK ends K y g) ∧ (connK ends K o y ∧ connK ends K x g)) := by
-- proof
  apply StatMech.Walls.gc7_core_pathCrossing_dichotomy ends K hnd o x y g hox hoy hog hxy hxg hyg hbdry hog_disc

/--
[gc7_core_allConnected_of_arcs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc7core.lean)
-/
@[path]
private lemma gc7_core_allConnected_of_arcs_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {ends : ι → Sym2 V}
  {K : Finset ι}
  {o x y g : V}
-- given
  (hox : connK ends K o x)
  (hoy : connK ends K o y)
  (hog : connK ends K o g) :
-- imply
  connK ends K o o ∧ connK ends K o x ∧ connK ends K o y ∧ connK ends K o g := by
-- proof
  apply StatMech.Walls.gc7_core_allConnected_of_arcs ends K hox hoy hog

/--
[gc7_core_pathCrossing_trichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc7core.lean)
-/
@[path]
private lemma gc7_core_pathCrossing_trichotomy_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {ends : ι → Sym2 V}
  {K : Finset ι}
  {o x y g : V}
-- given
  (hnd : ∀ i ∈ K, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (hbdry : sources ends K = ({o, x, y, g} : Finset V)) :
-- imply
  (connK ends K o g) ∨ (connK ends K o x ∧ connK ends K y g) ∨ (connK ends K o y ∧ connK ends K x g) := by
-- proof
  apply StatMech.Walls.gc7_core_pathCrossing_trichotomy ends K hnd o x y g hox hoy hog hxy hxg hyg hbdry

/--
[gc7_core_crossing_forces_oneCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc7core.lean)
-/
@[path]
private lemma gc7_core_crossing_forces_oneCluster_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {ends : ι → Sym2 V}
  {K : Finset ι}
  {o x y g w : V}
-- given
  (hox : connK ends K o x)
  (hyg : connK ends K y g)
  (hwo : connK ends K w o)
  (hwy : connK ends K w y) :
-- imply
  connK ends K o x ∧ connK ends K o y ∧ connK ends K o g := by
-- proof
  apply StatMech.Walls.gc7_core_crossing_forces_oneCluster ends K hox hyg hwo hwy

/--
[gc7_core_pathCrossing_dichotomy_edgeCopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc7core.lean)
-/
@[path]
private lemma gc7_core_pathCrossing_dichotomy_edgeCopy_eq
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
  (hbdry : sources (endsM G m) K = ({o, x, y, g} : Finset W))
  (hog_disc : ¬ connK (endsM G m) K o g) :
-- imply
  ((connK (endsM G m) K o x ∧ connK (endsM G m) K y g) ∨ (connK (endsM G m) K o y ∧ connK (endsM G m) K x g)) ∧ ¬ ((connK (endsM G m) K o x ∧ connK (endsM G m) K y g) ∧ (connK (endsM G m) K o y ∧ connK (endsM G m) K x g)) := by
-- proof
  apply StatMech.Walls.gc7_core_pathCrossing_dichotomy_edgeCopy G m K o x y g hox hoy hog hxy hxg hyg hbdry hog_disc

/--
[gc7_core_pathCrossing_trichotomy_edgeCopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc7core.lean)
-/
@[path]
private lemma gc7_core_pathCrossing_trichotomy_edgeCopy_eq
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
  (hbdry : sources (endsM G m) K = ({o, x, y, g} : Finset W)) :
-- imply
  (connK (endsM G m) K o g) ∨ (connK (endsM G m) K o x ∧ connK (endsM G m) K y g) ∨ (connK (endsM G m) K o y ∧ connK (endsM G m) K x g) := by
-- proof
  apply StatMech.Walls.gc7_core_pathCrossing_trichotomy_edgeCopy G m K o x y g hox hoy hog hxy hxg hyg hbdry

/--
[gc7_core_pairing1_arcs_realised](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc7core.lean)
-/
@[path]
private lemma gc7_core_pairing1_arcs_realised_eq
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
  {N₁ N₂ : Finset (Copy G m)}
  {o x y g : W}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (hN₁ : N₁ ⊆ K)
  (hN₂ : N₂ ⊆ K)
  (hb1 : sources (endsM G m) N₁ = ({o, x} : Finset W))
  (hb2 : sources (endsM G m) N₂ = ({y, g} : Finset W)) :
-- imply
  connK (endsM G m) K o x ∧ connK (endsM G m) K y g := by
-- proof
  apply StatMech.Walls.gc7_core_pairing1_arcs_realised G m K N₁ N₂ o x y g hox hoy hog hxy hxg hyg hN₁ hN₂ hb1 hb2

/--
[gc7_core_dichotomy_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc7core.lean)
-/
@[path]
private lemma gc7_core_dichotomy_nonvacuous_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype W]
  [DecidableEq W] :
-- imply
  let ends : Fin 2 → Sym2 (Fin 4) := fun i => if i = 0 then s(0, 1) else s(2, 3) sources ends (univ : Finset (Fin 2)) = ({0, 1, 2, 3} : Finset (Fin 4)) ∧ connK ends (univ : Finset (Fin 2)) 0 1 ∧ connK ends (univ : Finset (Fin 2)) 2 3 := by
-- proof
  apply StatMech.Walls.gc7_core_dichotomy_nonvacuous


-- created on 2026-10-23

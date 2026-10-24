import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gc89bmetricinjection
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc89b_reroute_boundary_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc89bmetricinjection.lean)
-/
@[path]
private lemma gc89b_reroute_boundary_empty_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K₁ P : Finset ι}
  {o g : W}
-- given
  (hP : P ⊆ K₁)
  (hK₁ : sources ends K₁ = ({o, g} : Finset W))
  (hPsrc : sources ends P = ({o, g} : Finset W)) :
-- imply
  sources ends (K₁ \ P) = (∅ : Finset W) := by
-- proof
  apply StatMech.Walls.gc89b_reroute_boundary_empty ends hP hK₁ hPsrc

/--
[gc89b_complement_union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc89bmetricinjection.lean)
-/
@[path]
private lemma gc89b_complement_union_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {m K₁ P : Finset ι}
-- given
  (hK₁m : K₁ ⊆ m)
  (hP : P ⊆ K₁) :
-- imply
  m \ (K₁ \ P) = (m \ K₁) ∪ P := by
-- proof
  apply StatMech.Walls.gc89b_complement_union m K₁ P hK₁m hP

/--
[gc89b_reroute_complement_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc89bmetricinjection.lean)
-/
@[path]
private lemma gc89b_reroute_complement_sources_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m K₁ P : Finset ι}
  {o g : W}
-- given
  (hK₁m : K₁ ⊆ m)
  (hP : P ⊆ K₁)
  (hK₁ : sources ends K₁ = ({o, g} : Finset W))
  (hPsrc : sources ends P = ({o, g} : Finset W)) :
-- imply
  sources ends (m \ (K₁ \ P)) = sources ends m := by
-- proof
  apply StatMech.Walls.gc89b_reroute_complement_sources ends hK₁m hP hK₁ hPsrc

/--
[gc89b_conn_og](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc89bmetricinjection.lean)
-/
@[path]
private lemma gc89b_conn_og_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m K₁ P : Finset ι}
  {o g : W}
-- given
  (hK₁m : K₁ ⊆ m)
  (hP : P ⊆ K₁)
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hPsrc : sources ends P = ({o, g} : Finset W))
  (hog : o ≠ g) :
-- imply
  connK ends (m \ (K₁ \ P)) o g := by
-- proof
  apply StatMech.Walls.gc89b_conn_og ends hK₁m hP hnd hPsrc hog

/--
[gc89b_conn_xg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc89bmetricinjection.lean)
-/
@[path]
private lemma gc89b_conn_xg_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m K₁ P : Finset ι}
  {x g : W}
-- given
  (hK₁m : K₁ ⊆ m)
  (hP : P ⊆ K₁)
  (hxg : connK ends (m \ K₁) x g) :
-- imply
  connK ends (m \ (K₁ \ P)) x g := by
-- proof
  apply StatMech.Walls.gc89b_conn_xg ends hK₁m hP hxg

/--
[gc89b_reroute_lands_allConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc89bmetricinjection.lean)
-/
@[path]
private lemma gc89b_reroute_lands_allConn_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m K₁ P : Finset ι}
  {o x y g : W}
-- given
  (hK₁m : K₁ ⊆ m)
  (hP : P ⊆ K₁)
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hsrc : sources ends m = ({o, x, y, g} : Finset W))
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxne : x ≠ y)
  (hxg' : x ≠ g)
  (hyg : y ≠ g)
  (hK₁ : sources ends K₁ = ({o, g} : Finset W))
  (hPsrc : sources ends P = ({o, g} : Finset W))
  (hxg : connK ends (m \ K₁) x g) :
-- imply
  connK ends (m \ (K₁ \ P)) o x ∧ connK ends (m \ (K₁ \ P)) o y ∧ connK ends (m \ (K₁ \ P)) o g := by
-- proof
  apply StatMech.Walls.gc89b_reroute_lands_allConn ends hK₁m hP hnd hsrc hox hoy hog hxne hxg' hyg hK₁ hPsrc hxg

/--
[gc89b_canonical_map_lands](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc89bmetricinjection.lean)
-/
@[path]
private lemma gc89b_canonical_map_lands_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m K₁ P : Finset ι}
  {o x y g : W}
-- given
  (hK₁m : K₁ ⊆ m)
  (hP : P ⊆ K₁)
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hsrc : sources ends m = ({o, x, y, g} : Finset W))
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxne : x ≠ y)
  (hxg' : x ≠ g)
  (hyg : y ≠ g)
  (hK₁ : sources ends K₁ = ({o, g} : Finset W))
  (hPsrc : sources ends P = ({o, g} : Finset W))
  (hxg : connK ends (m \ K₁) x g) :
-- imply
  (K₁ \ P) ⊆ m ∧ sources ends (K₁ \ P) = (∅ : Finset W) ∧ connK ends (m \ (K₁ \ P)) o x ∧ connK ends (m \ (K₁ \ P)) o y ∧ connK ends (m \ (K₁ \ P)) o g := by
-- proof
  apply StatMech.Walls.gc89b_canonical_map_lands ends hK₁m hP hnd hsrc hox hoy hog hxne hxg' hyg hK₁ hPsrc hxg

/--
[gc89b_exists_ogPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc89bmetricinjection.lean)
-/
@[path]
private lemma gc89b_exists_ogPath_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m K₁ : Finset ι}
  {o g : W}
-- given
  (hK₁m : K₁ ⊆ m)
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hog : o ≠ g)
  (hK₁ : sources ends K₁ = ({o, g} : Finset W)) :
-- imply
  ∃ P ⊆ K₁, sources ends P = ({o, g} : Finset W) := by
-- proof
  apply StatMech.Walls.gc89b_exists_ogPath ends hK₁m hnd hog hK₁

/--
[gc89b_ntEnds_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc89bmetricinjection.lean)
-/
@[path]
private lemma gc89b_ntEnds_sources_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  sources gc89b_ntEnds (univ : Finset (Fin 5)) = ({0, 1, 2, 3} : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.gc89b_ntEnds_sources

/--
[gc89b_metric_nontotal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc89bmetricinjection.lean)
-/
@[path]
private lemma gc89b_metric_nontotal_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  sources gc89b_ntEnds (({0} : Finset (Fin 5)) ∆ ({1, 3} : Finset (Fin 5))) = ({0, 3} : Finset (Fin 4)) ∧ ¬ gc89b_metricReroute gc89b_ntEnds 0 1 3 (({0} : Finset (Fin 5)), ({2} : Finset (Fin 5))) (({1, 3} : Finset (Fin 5)), (∅ : Finset (Fin 5))) := by
-- proof
  apply StatMech.Walls.gc89b_metric_nontotal

/--
[gc89b_canonical_collision](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc89bmetricinjection.lean)
-/
@[path]
private lemma gc89b_canonical_collision_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  (({1} : Finset (Fin 4)) \ ({1} : Finset (Fin 4)) = (∅ : Finset (Fin 4))) ∧ (({2} : Finset (Fin 4)) \ ({2} : Finset (Fin 4)) = (∅ : Finset (Fin 4))) ∧ sources gc88b_wredEnds ({1} : Finset (Fin 4)) = ({0, 3} : Finset (Fin 4)) ∧ sources gc88b_wredEnds ({2} : Finset (Fin 4)) = ({0, 3} : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.gc89b_canonical_collision

/--
[gc89b_tri_reroute_lands](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc89bmetricinjection.lean)
-/
@[path]
private lemma gc89b_tri_reroute_lands_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  sources gc87b_triEnds (({0} : Finset (Fin 3))) = ({0, 3} : Finset (Fin 4)) ∧ ({0} : Finset (Fin 3)) \ ({0} : Finset (Fin 3)) = (∅ : Finset (Fin 3)) ∧ connK gc87b_triEnds ((univ : Finset (Fin 3)) \ (∅ : Finset (Fin 3))) 0 1 ∧ connK gc87b_triEnds ((univ : Finset (Fin 3)) \ (∅ : Finset (Fin 3))) 0 2 ∧ connK gc87b_triEnds ((univ : Finset (Fin 3)) \ (∅ : Finset (Fin 3))) 0 3 := by
-- proof
  apply StatMech.Walls.gc89b_tri_reroute_lands

/--
[gc89b_metric_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc89bmetricinjection.lean)
-/
@[path]
private lemma gc89b_metric_status_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m K₁ P : Finset ι}
  {o x y g : W}
-- given
  (hK₁m : K₁ ⊆ m)
  (hP : P ⊆ K₁)
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hsrc : sources ends m = ({o, x, y, g} : Finset W))
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxne : x ≠ y)
  (hxg' : x ≠ g)
  (hyg : y ≠ g)
  (hK₁ : sources ends K₁ = ({o, g} : Finset W))
  (hPsrc : sources ends P = ({o, g} : Finset W))
  (hxg : connK ends (m \ K₁) x g) :
-- imply
  (sources ends (K₁ \ P) = (∅ : Finset W) ∧ connK ends (m \ (K₁ \ P)) o x ∧ connK ends (m \ (K₁ \ P)) o y ∧ connK ends (m \ (K₁ \ P)) o g) ∧ (∃ Q ⊆ K₁, sources ends Q = ({o, g} : Finset W)) := by
-- proof
  apply StatMech.Walls.gc89b_metric_status ends hK₁m hP hnd hsrc hox hoy hog hxne hxg' hyg hK₁ hPsrc hxg

/--
[gc89b_machine_findings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc89bmetricinjection.lean)
-/
@[path]
private lemma gc89b_machine_findings_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  True := by
-- proof
  apply StatMech.Walls.gc89b_machine_findings


-- created on 2026-10-23

import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.kc_raycounttrans
open Set SimpleGraph Function StatMech.Lattice StatMech StatMech.Walls


/--
[kc_rayCount_of_perm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_raycounttrans.lean)
-/
@[path]
private lemma kc_rayCount_of_perm_eq
  {a b : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {Vc' : (hypercubicLattice 2).Walk b b}
  {z : Site 2}
-- given
  (hperm : List.Perm Vc.edges Vc'.edges) :
-- imply
  jec_rayCount z Vc = jec_rayCount z Vc' := by
-- proof
  apply StatMech.Walls.kc_rayCount_of_perm Vc Vc' z hperm

/--
[kc_dartFace_trans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_raycounttrans.lean)
-/
@[path]
private lemma kc_dartFace_trans_eq
  {w : Site 2}
  {e : Dart} :
-- imply
  dartFace (transDart w e) = dartFace e + w := by
-- proof
  apply StatMech.Walls.kc_dartFace_trans w e

/--
[kc_rayEdge_trans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_raycounttrans.lean)
-/
@[path]
private lemma kc_rayEdge_trans_eq
  {w z x y : Site 2} :
-- imply
  jec_rayEdge (z + w) s(x + w, y + w) ↔ jec_rayEdge z s(x, y) := by
-- proof
  apply StatMech.Walls.kc_rayEdge_trans w z x y

/--
[kc_rayCount_trans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_raycounttrans.lean)
-/
@[path]
private lemma kc_rayCount_trans_eq
  {K : Set (Site 2)}
  {w : Site 2}
  {a : {e : Dart // IsBoundaryDart K e}}
  {z : Site 2} :
-- imply
  jec_rayCount (z + w) (mpl_orbitLoop (transSet w K) (transSub K w a)) = jec_rayCount z (mpl_orbitLoop K a) := by
-- proof
  apply StatMech.Walls.kc_rayCount_trans K w a z

/--
[kc_rayCount_trans_and_perm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_raycounttrans.lean)
-/
@[path]
private lemma kc_rayCount_trans_and_perm_eq :
-- imply
  (∀ (K : Set (Site 2)) (w : Site 2) (a : {e : Dart // IsBoundaryDart K e}) (z : Site 2), jec_rayCount (z + w) (mpl_orbitLoop (transSet w K) (transSub K w a)) = jec_rayCount z (mpl_orbitLoop K a)) ∧ (∀ {a b : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (Vc' : (hypercubicLattice 2).Walk b b) (z : Site 2), List.Perm Vc.edges Vc'.edges → jec_rayCount z Vc = jec_rayCount z Vc') := by
-- proof
  apply StatMech.Walls.kc_rayCount_trans_and_perm

/--
[kc_rayCount_trans'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_raycounttrans.lean)
-/
@[path]
private lemma kc_rayCount_trans'_eq
  {K : Set (Site 2)}
  {w : Site 2}
  {a : {e : Dart // IsBoundaryDart K e}}
  {z : Site 2} :
-- imply
  jec_rayCount z (mpl_orbitLoop K a) = jec_rayCount (z + w) (mpl_orbitLoop (transSet w K) (transSub K w a)) := by
-- proof
  apply StatMech.Walls.kc_rayCount_trans' K w a z


-- created on 2026-10-23

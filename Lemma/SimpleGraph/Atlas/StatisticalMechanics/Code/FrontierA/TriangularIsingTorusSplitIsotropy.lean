import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSplitIsotropy
open StatMech StatMech.FrontierA


/--
[triangularTorusSplitEmbedVertex_fst_mod_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitIsotropy.lean)
-/
@[path]
private lemma triangularTorusSplitEmbedVertex_fst_mod_three_eq
  {L : Nat}
  [Fact (2 < L)]
  {p : KWDartPort (triangularTorusGraph L)} :
-- imply
  (triangularTorusSplitEmbedVertex L p).1.val % 3 = (triangularTorusSplitOffset (triangularTorusGraphDartDirection L (kwDartOfPort (triangularTorusGraph L) p))).1 := by
-- proof
  apply StatMech.FrontierA.triangularTorusSplitEmbedVertex_fst_mod_three L p

/--
[triangularTorusSplitEmbedVertex_snd_mod_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitIsotropy.lean)
-/
@[path]
private lemma triangularTorusSplitEmbedVertex_snd_mod_three_eq
  {L : Nat}
  [Fact (2 < L)]
  {p : KWDartPort (triangularTorusGraph L)} :
-- imply
  (triangularTorusSplitEmbedVertex L p).2.val % 3 = (triangularTorusSplitOffset (triangularTorusGraphDartDirection L (kwDartOfPort (triangularTorusGraph L) p))).2 := by
-- proof
  apply StatMech.FrontierA.triangularTorusSplitEmbedVertex_snd_mod_three L p

/--
[triangular_zmod_val_add_one_mod_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitIsotropy.lean)
-/
@[path]
private lemma triangular_zmod_val_add_one_mod_three_eq
  {L : Nat}
  [Fact (2 < L)]
  {z : ZMod (3 * L)} :
-- imply
  (z + 1).val % 3 = (z.val + 1) % 3 := by
-- proof
  apply StatMech.FrontierA.triangular_zmod_val_add_one_mod_three L z

/--
[triangular_nat_add_one_mod_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitIsotropy.lean)
-/
@[path]
private lemma triangular_nat_add_one_mod_three_eq
  {n : Nat} :
-- imply
  (n + 1) % 3 = (n % 3 + 1) % 3 := by
-- proof
  apply StatMech.FrontierA.triangular_nat_add_one_mod_three n

/--
[triangularTorusNortheastEdge_eq_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitIsotropy.lean)
-/
@[path]
private lemma triangularTorusNortheastEdge_eq_pair_eq
  {N : Nat}
  [Fact (2 < N)]
  {z : ZMod N × ZMod N} :
-- imply
  triangularTorusNortheastEdge N z = s(z, (z.1 + 1, z.2 + 1)) := by
-- proof
  apply StatMech.FrontierA.triangularTorusNortheastEdge_eq_pair N z

/--
[triangularTorusSplitOffset_no_diagonalCorner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitIsotropy.lean)
-/
@[path]
private lemma triangularTorusSplitOffset_no_diagonalCorner_eq :
-- imply
  ∀ a b c : Fin 6, (triangularTorusSplitOffset b).1 = ((triangularTorusSplitOffset a).1 + 1) % 3 → (triangularTorusSplitOffset b).2 = ((triangularTorusSplitOffset a).2 + 1) % 3 → (triangularTorusSplitOffset c).1 = ((triangularTorusSplitOffset a).1 + 1) % 3 → (triangularTorusSplitOffset c).2 = (triangularTorusSplitOffset a).2 → False := by
-- proof
  apply StatMech.FrontierA.triangularTorusSplitOffset_no_diagonalCorner

/--
[triangularTorusSplitEmbed_diagonalCorner_not_mem_range](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitIsotropy.lean)
-/
@[path]
private lemma triangularTorusSplitEmbed_diagonalCorner_not_mem_range_eq
  {L : Nat}
  [Fact (2 < L)]
  {p q r : KWDartPort (triangularTorusGraph L)}
  {z : ZMod (3 * L) × ZMod (3 * L)}
-- given
  (hedge : s(triangularTorusSplitEmbedVertex L p, triangularTorusSplitEmbedVertex L q) = triangularTorusNortheastEdge (3 * L) z) :
-- imply
  triangularTorusSplitEmbedVertex L r ≠ (z.1 + 1, z.2) := by
-- proof
  apply StatMech.FrontierA.triangularTorusSplitEmbed_diagonalCorner_not_mem_range L p q r z hedge

/--
[triangularSquareExpansion_vertex_carrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitIsotropy.lean)
-/
@[path]
private lemma triangularSquareExpansion_vertex_carrier_eq
  {N : Nat}
  [Fact (2 < N)]
  {F : Finset (Sym2 (ZMod N × ZMod N))}
  {edge : Sym2 (ZMod N × ZMod N)}
  {z : ZMod N × ZMod N}
-- given
  (hedge : edge ∈ triangularSquareExpansion N F)
  (hz : z ∈ edge) :
-- imply
  (∃ original ∈ F, z ∈ original) ∨ ∃ p, triangularTorusNortheastEdge N p ∈ F ∧ z = (p.1 + 1, p.2) := by
-- proof
  apply StatMech.FrontierA.triangularSquareExpansion_vertex_carrier N F edge hedge z hz

/--
[triangularTorusSplitEmbedWalk_diagonalCorner_not_mem_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitIsotropy.lean)
-/
@[path]
private lemma triangularTorusSplitEmbedWalk_diagonalCorner_not_mem_support_eq
  {L : Nat}
  [Fact (2 < L)]
  {u v x y : KWDartPort (triangularTorusGraph L)}
  {p : (kwOrderedDartPortSplitGraph (triangularTorusGraph L) (triangularTorusLocalPortOrder L)).Walk u v}
  {q : (kwOrderedDartPortSplitGraph (triangularTorusGraph L) (triangularTorusLocalPortOrder L)).Walk x y}
  {z : ZMod (3 * L) × ZMod (3 * L)}
-- given
  (hdiag : triangularTorusNortheastEdge (3 * L) z ∈ (triangularTorusSplitEmbedWalk L p).edges.toFinset) :
-- imply
  (z.1 + 1, z.2) ∉ (triangularTorusSplitEmbedWalk L q).support := by
-- proof
  apply StatMech.FrontierA.triangularTorusSplitEmbedWalk_diagonalCorner_not_mem_support L p q z hdiag

/--
[triangularTorusSplitEmbedWalk_squareExpansion_incCount_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitIsotropy.lean)
-/
@[path]
private lemma triangularTorusSplitEmbedWalk_squareExpansion_incCount_disjoint_eq
  {L : Nat}
  [Fact (2 < L)]
  {u v : KWDartPort (triangularTorusGraph L)}
  {p : (kwOrderedDartPortSplitGraph (triangularTorusGraph L) (triangularTorusLocalPortOrder L)).Walk u u}
  {q : (kwOrderedDartPortSplitGraph (triangularTorusGraph L) (triangularTorusLocalPortOrder L)).Walk v v}
-- given
  (hdisjoint : Disjoint (triangularTorusSplitEmbedWalk L p).toSubgraph.verts (triangularTorusSplitEmbedWalk L q).toSubgraph.verts) :
-- imply
  ∀ z, incCount (triangularSquareExpansion (3 * L) (triangularTorusSplitEmbedWalk L p).edges.toFinset) z = 0 ∨ incCount (triangularSquareExpansion (3 * L) (triangularTorusSplitEmbedWalk L q).edges.toFinset) z = 0 := by
-- proof
  apply StatMech.FrontierA.triangularTorusSplitEmbedWalk_squareExpansion_incCount_disjoint L p q hdisjoint

/--
[surfaceIntersection_genus_one_eq_ons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitIsotropy.lean)
-/
@[path]
private lemma surfaceIntersection_genus_one_eq_ons_eq
-- given
  (h k : Fin 2 × Fin 2) :
-- imply
  surfaceIntersection (fun _ : Fin 1 => h.1, fun _ : Fin 1 => h.2) (fun _ : Fin 1 => k.1, fun _ : Fin 1 => k.2) = ons_homologyIntersection h k := by
-- proof
  apply StatMech.FrontierA.surfaceIntersection_genus_one_eq_ons h k

/--
[triangularTorus_localAngularSplit_disjointCycleIsotropic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitIsotropy.lean)
-/
@[path]
private lemma triangularTorus_localAngularSplit_disjointCycleIsotropic_eq
  {L : Nat}
  [Fact (2 < L)] :
-- imply
  SurfaceDisjointCycleIsotropic (kwOrderedDartPortSplitGraph (triangularTorusGraph L) (triangularTorusLocalPortOrder L)) (kwOrderedSplitEdgeClass (triangularTorusSurfaceEdgeClass L)) := by
-- proof
  apply StatMech.FrontierA.triangularTorus_localAngularSplit_disjointCycleIsotropic L


-- created on 2026-10-23

import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.KacWardAngularPortGeometry
open StatMech StatMech.FrontierA


/--
[KWStraightLineEmbedding.dartClosedEdge_isCompact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortGeometry.lean)
-/
@[path]
private lemma dartClosedEdge_isCompact_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {d : G.Dart} :
-- imply
  IsCompact (embedding.dartClosedEdge d) := by
-- proof
  apply StatMech.FrontierA.KWStraightLineEmbedding.dartClosedEdge_isCompact embedding d

/--
[KWStraightLineEmbedding.dartClosedEdge_isClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortGeometry.lean)
-/
@[path]
private lemma dartClosedEdge_isClosed_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {d : G.Dart} :
-- imply
  IsClosed (embedding.dartClosedEdge d) := by
-- proof
  apply StatMech.FrontierA.KWStraightLineEmbedding.dartClosedEdge_isClosed embedding d

/--
[KWStraightLineEmbedding.vertex_not_mem_dartClosedEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortGeometry.lean)
-/
@[path]
private lemma vertex_not_mem_dartClosedEdge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {v : V}
  {d : G.Dart}
-- given
  (hvfst : v ≠ d.fst)
  (hvsnd : v ≠ d.snd) :
-- imply
  embedding.vertex v ∉ embedding.dartClosedEdge d := by
-- proof
  apply StatMech.FrontierA.KWStraightLineEmbedding.vertex_not_mem_dartClosedEdge embedding v d hvfst hvsnd

/--
[KWStraightLineEmbedding.singleton_vertex_disjoint_dartClosedEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortGeometry.lean)
-/
@[path]
private lemma singleton_vertex_disjoint_dartClosedEdge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {v : V}
  {d : G.Dart}
-- given
  (hvfst : v ≠ d.fst)
  (hvsnd : v ≠ d.snd) :
-- imply
  Disjoint ({embedding.vertex v} : Set ℂ) (embedding.dartClosedEdge d) := by
-- proof
  apply StatMech.FrontierA.KWStraightLineEmbedding.singleton_vertex_disjoint_dartClosedEdge embedding v d hvfst hvsnd

/--
[KWStraightLineEmbedding.exists_uniform_vertex_separation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortGeometry.lean)
-/
@[path]
private lemma exists_uniform_vertex_separation_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G} :
-- imply
  ∃ r : ℝ≥0, 0 < r ∧ ∀ v w : V, v ≠ w → (r : ℝ) < dist (embedding.vertex v) (embedding.vertex w) := by
-- proof
  apply StatMech.FrontierA.KWStraightLineEmbedding.exists_uniform_vertex_separation embedding

/--
[KWStraightLineEmbedding.exists_uniform_edge_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortGeometry.lean)
-/
@[path]
private lemma exists_uniform_edge_length_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G} :
-- imply
  ∃ r : ℝ≥0, 0 < r ∧ ∀ d : G.Dart, (r : ℝ) < ‖embedding.vertex d.snd - embedding.vertex d.fst‖ := by
-- proof
  apply StatMech.FrontierA.KWStraightLineEmbedding.exists_uniform_edge_length embedding

/--
[KWStraightLineEmbedding.exists_uniform_vertex_edge_separation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortGeometry.lean)
-/
@[path]
private lemma exists_uniform_vertex_edge_separation_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G} :
-- imply
  ∃ r : ℝ≥0, 0 < r ∧ ∀ (v : V) (d : G.Dart), v ≠ d.fst → v ≠ d.snd → ∀ y ∈ embedding.dartClosedEdge d, (r : ℝ) < dist (embedding.vertex v) y := by
-- proof
  apply StatMech.FrontierA.KWStraightLineEmbedding.exists_uniform_vertex_edge_separation embedding

/--
[KWStraightLineEmbedding.exists_angularPortRadiusData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortGeometry.lean)
-/
@[path]
private lemma exists_angularPortRadiusData_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G} :
-- imply
  Nonempty (KWAngularPortRadiusData embedding) := by
-- proof
  apply StatMech.FrontierA.KWStraightLineEmbedding.exists_angularPortRadiusData embedding

/--
[KWStraightLineEmbedding.norm_dartUnit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortGeometry.lean)
-/
@[path]
private lemma norm_dartUnit_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {d : G.Dart} :
-- imply
  ‖embedding.dartUnit d‖ = 1 := by
-- proof
  apply StatMech.FrontierA.KWStraightLineEmbedding.norm_dartUnit embedding d

/--
[KWStraightLineEmbedding.dartUnit_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortGeometry.lean)
-/
@[path]
private lemma dartUnit_ne_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {d : G.Dart} :
-- imply
  embedding.dartUnit d ≠ 0 := by
-- proof
  apply StatMech.FrontierA.KWStraightLineEmbedding.dartUnit_ne_zero embedding d

/--
[KWStraightLineEmbedding.dartUnit_eq_iff_arg_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortGeometry.lean)
-/
@[path]
private lemma dartUnit_eq_iff_arg_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {d e : G.Dart} :
-- imply
  embedding.dartUnit d = embedding.dartUnit e ↔ Complex.arg (embedding.vertex d.snd - embedding.vertex d.fst) = Complex.arg (embedding.vertex e.snd - embedding.vertex e.fst) := by
-- proof
  apply StatMech.FrontierA.KWStraightLineEmbedding.dartUnit_eq_iff_arg_eq embedding d e

/--
[KWStraightLineEmbedding.dartUnit_ne_of_outgoing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortGeometry.lean)
-/
@[path]
private lemma dartUnit_ne_of_outgoing_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {d e : G.Dart}
-- given
  (hfst : d.fst = e.fst)
  (hne : d ≠ e) :
-- imply
  embedding.dartUnit d ≠ embedding.dartUnit e := by
-- proof
  apply StatMech.FrontierA.KWStraightLineEmbedding.dartUnit_ne_of_outgoing embedding hfst hne

/--
[KWStraightLineEmbedding.dartUnit_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortGeometry.lean)
-/
@[path]
private lemma dartUnit_symm_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {d : G.Dart} :
-- imply
  embedding.dartUnit d.symm = -embedding.dartUnit d := by
-- proof
  apply StatMech.FrontierA.KWStraightLineEmbedding.dartUnit_symm embedding d

/--
[KWStraightLineEmbedding.dartVector_eq_norm_mul_dartUnit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortGeometry.lean)
-/
@[path]
private lemma dartVector_eq_norm_mul_dartUnit_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {d : G.Dart} :
-- imply
  embedding.vertex d.snd - embedding.vertex d.fst = (‖embedding.vertex d.snd - embedding.vertex d.fst‖ : ℂ) * embedding.dartUnit d := by
-- proof
  apply StatMech.FrontierA.KWStraightLineEmbedding.dartVector_eq_norm_mul_dartUnit embedding d

/--
[dist_kwAngularPortVertex_owner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortGeometry.lean)
-/
@[path]
private lemma dist_kwAngularPortVertex_owner_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {r : ℝ}
  {p : KWDartPort G} :
-- imply
  dist (kwAngularPortVertex embedding r p) (embedding.vertex p.1) = := by
-- proof
  apply StatMech.FrontierA.dist_kwAngularPortVertex_owner embedding r p

/--
[kwAngularPortVertex_sub_owner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortGeometry.lean)
-/
@[path]
private lemma kwAngularPortVertex_sub_owner_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {r : ℝ}
  {p : KWDartPort G} :
-- imply
  kwAngularPortVertex embedding r p - embedding.vertex p.1 = (r : ℂ) * embedding.dartUnit (kwDartOfPort G p) := by
-- proof
  apply StatMech.FrontierA.kwAngularPortVertex_sub_owner embedding r p

/--
[kwAngularPortVertex_matching_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortGeometry.lean)
-/
@[path]
private lemma kwAngularPortVertex_matching_sub_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {r : ℝ}
  {p q : KWDartPort G}
-- given
  (hmatching : kwDartOfPort G q = (kwDartOfPort G p).symm) :
-- imply
  kwAngularPortVertex embedding r q - kwAngularPortVertex embedding r p = ((‖embedding.vertex (kwDartOfPort G p).snd - embedding.vertex (kwDartOfPort G p).fst‖ - 2 * r : ℝ) : ℂ) * embedding.dartUnit (kwDartOfPort G p) := by
-- proof
  apply StatMech.FrontierA.kwAngularPortVertex_matching_sub embedding r hmatching

/--
[kwAngularPortVertex_matching_positive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortGeometry.lean)
-/
@[path]
private lemma kwAngularPortVertex_matching_positive_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {r : ℝ}
  {p q : KWDartPort G}
-- given
  (hmatching : kwDartOfPort G q = (kwDartOfPort G p).symm)
  (hr : 2 * r < ‖embedding.vertex (kwDartOfPort G p).snd - embedding.vertex (kwDartOfPort G p).fst‖) :
-- imply
  ∃ c : ℝ, 0 < c ∧ kwAngularPortVertex embedding r q - kwAngularPortVertex embedding r p = (c : ℂ) * embedding.dartUnit (kwDartOfPort G p) := by
-- proof
  apply StatMech.FrontierA.kwAngularPortVertex_matching_positive embedding hmatching hr

/--
[kwAngularPortVertex_eq_iff_dartUnit_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortGeometry.lean)
-/
@[path]
private lemma kwAngularPortVertex_eq_iff_dartUnit_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {r : ℝ}
  {p q : KWDartPort G}
-- given
  (hr : r ≠ 0)
  (howner : p.1 = q.1) :
-- imply
  kwAngularPortVertex embedding r p = kwAngularPortVertex embedding r q ↔ embedding.dartUnit (kwDartOfPort G p) = embedding.dartUnit (kwDartOfPort G q) := by
-- proof
  apply StatMech.FrontierA.kwAngularPortVertex_eq_iff_dartUnit_eq embedding hr howner

/--
[kwAngularPortVertex_ne_of_same_owner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortGeometry.lean)
-/
@[path]
private lemma kwAngularPortVertex_ne_of_same_owner_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {r : ℝ}
  {p q : KWDartPort G}
-- given
  (hr : r ≠ 0)
  (howner : p.1 = q.1)
  (hpq : p ≠ q) :
-- imply
  kwAngularPortVertex embedding r p ≠ kwAngularPortVertex embedding r q := by
-- proof
  apply StatMech.FrontierA.kwAngularPortVertex_ne_of_same_owner embedding hr howner hpq

/--
[KWAngularPortRadiusData.portVertex_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortGeometry.lean)
-/
@[path]
private lemma portVertex_injective_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {data : KWAngularPortRadiusData embedding} :
-- imply
  Function.Injective (kwAngularPortVertex embedding (data.radius : ℝ)) := by
-- proof
  apply StatMech.FrontierA.KWAngularPortRadiusData.portVertex_injective data

/--
[KWAngularPortRadiusData.portVertex_mem_sphere](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortGeometry.lean)
-/
@[path]
private lemma portVertex_mem_sphere_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {data : KWAngularPortRadiusData embedding}
  {p : KWDartPort G} :
-- imply
  kwAngularPortVertex embedding (data.radius : ℝ) p ∈ Metric.sphere (embedding.vertex p.1) (data.radius : ℝ) := by
-- proof
  apply StatMech.FrontierA.KWAngularPortRadiusData.portVertex_mem_sphere data p

/--
[KWAngularPortRadiusData.internalChord_mem_ball](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortGeometry.lean)
-/
@[path]
private lemma internalChord_mem_ball_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {data : KWAngularPortRadiusData embedding}
  {p q : KWDartPort G}
  {z : ℂ}
-- given
  (howner : p.1 = q.1)
  (hpq : p ≠ q)
  (hz : Sbtw ℝ (kwAngularPortVertex embedding (data.radius : ℝ) p) z (kwAngularPortVertex embedding (data.radius : ℝ) q)) :
-- imply
  z ∈ Metric.ball (embedding.vertex p.1) (data.radius : ℝ) := by
-- proof
  apply StatMech.FrontierA.KWAngularPortRadiusData.internalChord_mem_ball data howner hpq hz

/--
[KWAngularPortRadiusData.internalChords_disjoint_of_owner_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortGeometry.lean)
-/
@[path]
private lemma internalChords_disjoint_of_owner_ne_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {data : KWAngularPortRadiusData embedding}
  {p q p' q' : KWDartPort G}
-- given
  (hpowner : p.1 = q.1)
  (hpq : p ≠ q)
  (hqowner : p'.1 = q'.1)
  (hpq' : p' ≠ q')
  (howners : p.1 ≠ p'.1) :
-- imply
  Disjoint {z : ℂ | Sbtw ℝ (kwAngularPortVertex embedding (data.radius : ℝ) p) z (kwAngularPortVertex embedding (data.radius : ℝ) q)} {z : ℂ | Sbtw ℝ (kwAngularPortVertex embedding (data.radius : ℝ) p') z (kwAngularPortVertex embedding (data.radius : ℝ) q')} := by
-- proof
  apply StatMech.FrontierA.KWAngularPortRadiusData.internalChords_disjoint_of_owner_ne data hpowner hpq hqowner hpq' howners


-- created on 2026-10-23

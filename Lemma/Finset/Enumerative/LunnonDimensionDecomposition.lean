import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Combinatorics.Enumerative.LunnonDimensionDecomposition.Part9
open scoped BigOperators
open MetaMathlibExt


namespace MetaMathlibExt

/--
[faceAdjacent_symm_aux](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LunnonDimensionDecomposition.lean)
-/
@[path]
private lemma faceAdjacent_symm_aux (d : ℕ) (x y : latticeCell d) :
  faceAdjacent d x y → faceAdjacent d y x :=
  fun ⟨k, hagree, hstep⟩ =>
    ⟨k, fun j hj => (hagree j hj).symm, by rcases hstep with h | h <;> [right; left] <;> omega⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[faceAdjacent_irrefl_aux](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LunnonDimensionDecomposition.lean)
-/
@[path]
private lemma faceAdjacent_irrefl_aux (d : ℕ) (x : latticeCell d) : ¬ faceAdjacent d x x := by
  rintro ⟨k, _, hstep⟩
  obtain h | h <;> omega := hstep

end MetaMathlibExt

namespace MetaMathlibExt

/--
[polyGraph_connected_aux](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LunnonDimensionDecomposition.lean)
-/
@[path]
private lemma polyGraph_connected_aux (d : ℕ) (S : Finset (latticeCell d))
  (hP : isPolycubeCells d S) : (polyGraph_aux d S).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  obtain ⟨x0, hx0⟩ := hP.1
  refine ⟨⟨x0, hx0⟩, fun v => ?_⟩
  rw [SimpleGraph.reachable_iff_reflTransGen]
  obtain ⟨y, hy⟩ := v
  have hRT := hP.2 x0 hx0 y hy
  have lift : ∀ (z : latticeCell d)
    (h : Relation.ReflTransGen
      (fun a b : latticeCell d => faceAdjacent d a b ∧ a ∈ S ∧ b ∈ S) x0 z)
    (hz : z ∈ S),
      Relation.ReflTransGen (fun a b : ↥S => (polyGraph_aux d S).Adj a b)
        ⟨x0, hx0⟩ ⟨z, hz⟩ :=
    fun z h => Relation.ReflTransGen.rec
      (motive := fun z _ => ∀ hz : z ∈ S,
        Relation.ReflTransGen (fun a b : ↥S => (polyGraph_aux d S).Adj a b)
          ⟨x0, hx0⟩ ⟨z, hz⟩)
      (fun hz => by
        have he : (⟨x0, hx0⟩ : ↥S) = ⟨x0, hz⟩ := Subtype.ext rfl
        rw [he])
      (fun (hprev : Relation.ReflTransGen _ x0 _) (hstep : faceAdjacent d _ _ ∧ _ ∈ S ∧ _ ∈ S)
        (ih : ∀ hz, _) (hz : _ ∈ S) => by
        obtain ⟨hadj, hbS, _hcS⟩ := hstep
        have ih' := ih hbS
        have hsingle : (polyGraph_aux d S).Adj ⟨_, hbS⟩ (⟨_, hz⟩ : ↥S) := hadj
        exact ih'.tail hsingle)
      h
  exact lift y hRT hy

end MetaMathlibExt

namespace MetaMathlibExt

/--
[faceAdjacent_axis_unique_aux](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LunnonDimensionDecomposition.lean)
-/
@[path]
private lemma faceAdjacent_axis_unique_aux (d : ℕ) (x y : latticeCell d) (k k' : Fin d)
  (_h : faceAdjacent d x y)
  (hagree : ∀ j : Fin d, j ≠ k' → x j = y j)
  (hdiff : x k ≠ y k) : k = k' := by
  by_contra hne
  exact hdiff (hagree k hne)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[faceAdjacent_axis_unique_aux2](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LunnonDimensionDecomposition.lean)
-/
@[path]
private lemma faceAdjacent_axis_unique_aux2 (d : ℕ) (x y : latticeCell d) (k k' : Fin d)
  (hagree : ∀ j : Fin d, j ≠ k' → x j = y j)
  (hdiff : x k ≠ y k) : k = k' := by
  by_contra hne
  exact hdiff (hagree k hne)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[walk_exists_edge_diff_generic_aux](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LunnonDimensionDecomposition.lean)
-/
@[path]
private lemma walk_exists_edge_diff_generic_aux (d : ℕ) (S : Finset (latticeCell d))
  (G : SimpleGraph ↥S) (k : Fin d)
  {a b : ↥S} (w : G.Walk a b)
  (hdiff : ((a : latticeCell d) k) ≠ ((b : latticeCell d) k)) :
  ∃ e ∈ w.edges, ∃ u v : ↥S, e = s(u, v) ∧ G.Adj u v ∧
    ((u : latticeCell d) k) ≠ ((v : latticeCell d) k) := by
  induction w with
  | nil => simp at hdiff
  | @cons u v w hadj tail ih =>
    by_cases heq : ((u : latticeCell d) k) = ((v : latticeCell d) k)
    · have hdiff' : ((v : latticeCell d) k) ≠ ((w : latticeCell d) k) := by omega
      obtain ⟨e, he, u', v', heq2, hadj', hne⟩ := ih hdiff'
      refine ⟨e, ?_, u', v', heq2, hadj', hne⟩
      rw [SimpleGraph.Walk.edges_cons]
      exact List.mem_cons_of_mem _ he
    · refine ⟨s(u, v), ?_, u, v, rfl, hadj, heq⟩
      rwa [SimpleGraph.Walk.edges_cons]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[support_card_lt_aux](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LunnonDimensionDecomposition.lean)
-/
@[path]
private lemma support_card_lt_aux (d n : ℕ) (S : Finset (latticeCell d))
  (hP : isPolycubeCells d S) (hn : S.card = n) :
  (supportFinset_aux d S).card < n := by
  classical
  have hconn := polyGraph_connected_aux d S hP
  obtain ⟨T, hle, hTree⟩ := SimpleGraph.Connected.exists_isTree_le hconn
  have : DecidableEq ↥S := Classical.typeDecidableEq _
  have : DecidableRel T.Adj := Classical.decRel _
  have := SimpleGraph.fintypeEdgeSet T
  have hcard := hTree.card_edgeFinset
  rw [Fintype.card_coe, hn] at hcard
  let axisSet : Sym2 ↥S → Finset (Fin d) := fun e =>
    Finset.univ.filter (fun k => ∃ u v : ↥S, e = s(u, v) ∧ T.Adj u v ∧
      ((u : latticeCell d) k) ≠ ((v : latticeCell d) k))
  have haxis1 : ∀ e ∈ T.edgeFinset, (axisSet e).card ≤ 1 := by
    intro e he
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [axisSet, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    obtain ⟨u1, v1, he1, hadj1, hne1⟩ := ha
    obtain ⟨u2, v2, he2, hadj2, hne2⟩ := hb
    have hf1 : faceAdjacent d (u1 : latticeCell d) (v1 : latticeCell d) := hle hadj1
    obtain ⟨k1, hagree1, _⟩ := hf1
    have ha1 : a = k1 := faceAdjacent_axis_unique_aux2 d _ _ a k1 hagree1 hne1
    have heq : s(u1, v1) = s(u2, v2) := by rw [← he1, ← he2]
    rw [Sym2.eq_iff] at heq
    obtain ⟨rfl, rfl⟩ | ⟨h1, h2⟩ := heq
    · have hne1' : ((u1 : latticeCell d) b) ≠ ((v1 : latticeCell d) b) := hne2
      have hb1 : b = k1 := faceAdjacent_axis_unique_aux2 d _ _ b k1 hagree1 hne1'
      omega
    · subst h1
      subst h2
      simp only [ne_eq]at hne2
      have hne1' : ((u1 : latticeCell d) b) ≠ ((v1 : latticeCell d) b) := Ne.symm hne2
      have hb1 : b = k1 := faceAdjacent_axis_unique_aux2 d _ _ b k1 hagree1 hne1'
      omega
  have hsub : supportFinset_aux d S ⊆ T.edgeFinset.biUnion axisSet := by
    intro k hk
    simp only [supportFinset_aux, Finset.mem_filter, Finset.mem_univ, true_and] at hk
    obtain ⟨x, hx, y, hy, hxy⟩ := hk
    have hTconn := hTree.connected
    rw [SimpleGraph.connected_iff_exists_forall_reachable] at hTconn
    obtain ⟨r, hr⟩ := hTconn
    have hreach : T.Reachable ⟨x, hx⟩ ⟨y, hy⟩ :=
      (hr ⟨x, hx⟩).symm.trans (hr ⟨y, hy⟩)
    have hex : ∃ w : T.Walk ⟨x, hx⟩ ⟨y, hy⟩,
      ∃ e ∈ w.edges, ∃ u v : ↥S, e = s(u, v) ∧ T.Adj u v ∧
        ((u : latticeCell d) k) ≠ ((v : latticeCell d) k) := by
      refine hreach.elim_path (fun p => ?_)
      obtain ⟨w, _hw⟩ := p
      have hdiff : (((⟨x, hx⟩ : ↥S) : latticeCell d) k) ≠
        (((⟨y, hy⟩ : ↥S) : latticeCell d) k) := hxy
      refine ⟨w, walk_exists_edge_diff_generic_aux d S T k w hdiff⟩
    obtain ⟨w, e, he, u, v, heq, hadj, hne⟩ := hex
    have hedge : e ∈ T.edgeSet := w.edges_subset_edgeSet he
    have hefin : e ∈ T.edgeFinset := (SimpleGraph.mem_edgeFinset).mpr hedge
    exact Finset.mem_biUnion.mpr ⟨e, hefin, by
      simp only [axisSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨u, v, heq, hadj, hne⟩⟩
  have h1 : (supportFinset_aux d S).card ≤ (T.edgeFinset.biUnion axisSet).card :=
    Finset.card_le_card hsub
  have h2 : (T.edgeFinset.biUnion axisSet).card ≤
    ∑ e ∈ T.edgeFinset, (axisSet e).card := Finset.card_biUnion_le
  have hsum : ∑ e ∈ T.edgeFinset, (axisSet e).card ≤ T.edgeFinset.card := by
    calc ∑ e ∈ T.edgeFinset, (axisSet e).card
      ≤ ∑ _e ∈ T.edgeFinset, 1 := Finset.sum_le_sum haxis1
      _ = T.edgeFinset.card := by simp
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[vanish_DX_zero_aux](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LunnonDimensionDecomposition.lean)
-/
@[path]
private lemma vanish_DX_zero_aux (n : ℕ) (hn : 1 < n) : properFixedPolycubeCount n 0 = 0 := by
  unfold properFixedPolycubeCount
  rw [Nat.card_eq_zero]
  left
  constructor
  intro Q
  obtain ⟨P, _hP⟩ := Q
  obtain ⟨S, ⟨_hS, hnS, _hC⟩⟩ := P
  -- S : Finset (latticeCell 0) with card = n > 1, but Subsingleton gives ≤1
  have hle : S.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a _ b _
    exact Subsingleton.elim a b
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[fiber_card_eq_DX_aux](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LunnonDimensionDecomposition.lean)
-/
@[path]
private lemma fiber_card_eq_DX_aux (d n : ℕ) (A : Finset (Fin d)) :
  Nat.card (fiberSet_aux d n A) = properFixedPolycubeCount n A.card := by
  unfold properFixedPolycubeCount
  exact Nat.card_congr (fiberEquivProper_aux d n A)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[card_eq_sum_fiber_aux](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LunnonDimensionDecomposition.lean)
-/
@[path]
private lemma card_eq_sum_fiber_aux (d n : ℕ) :
  Nat.card (fixedPolycube d n) =
    ∑ A : Finset (Fin d), Nat.card (fiberSet_aux d n A) := by
  rw [← Nat.card_sigma]
  exact Nat.card_congr (sigmaFiberEquiv_aux d n).symm

end MetaMathlibExt

namespace MetaMathlibExt

/--
[sum_fiber_eq_range_aux](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LunnonDimensionDecomposition.lean)
-/
@[path]
private lemma sum_fiber_eq_range_aux (d n : ℕ) :
  (∑ A : Finset (Fin d), Nat.card (fiberSet_aux d n A)) =
    ∑ m ∈ Finset.range (d + 1), d.choose m * properFixedPolycubeCount n m := by
  simp_rw [fiber_card_eq_DX_aux d n]
  have h2 := Finset.sum_powerset_apply_card (α := ℕ)
    (fun m => properFixedPolycubeCount n m) (x := (Finset.univ : Finset (Fin d)))
  rw [Finset.card_univ, Fintype.card_fin] at h2
  rw [← Finset.powerset_univ]
  rw [h2]
  apply Finset.sum_congr rfl
  intro m _
  rw [nsmul_eq_mul, Nat.cast_id]

end MetaMathlibExt

/--
[lunnon_fixed_polycube_dimension_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LunnonDimensionDecomposition.lean)
-/
@[path]
private lemma lunnon_fixed_polycube_dimension_decomposition_eq
  {d n : ℕ}
-- given
  (hn : 1 < n) :
-- imply
  fixedPolycubeCount d n =
    Finset.sum (Finset.Ico 1 n) (fun i => Nat.choose d i * properFixedPolycubeCount n i) := by
-- proof
  apply MetaMathlibExt.lunnon_fixed_polycube_dimension_decomposition d n hn


-- created on 2026-10-20
-- updated on 2026-10-26

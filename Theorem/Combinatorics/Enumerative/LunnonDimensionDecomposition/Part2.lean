/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LunnonDimensionDecomposition.lean -/

import Mathlib.Order.Interval.Finset.Nat
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Choose.Sum
import Def.Combinatorics.Enumerative.LunnonDimensionDecomposition.Part2


section

namespace MetaMathlibExt

open scoped BigOperators

lemma walk_coord_le_aux (d : ℕ) (S : Finset (latticeCell d)) (k : Fin d)
    {a b : ↥S} (w : (polyGraph_aux d S).Walk a b) :
    |(((b : latticeCell d) k) - ((a : latticeCell d) k))| ≤ (w.length : ℤ) := by
  induction w with
  | nil => simp
  | @cons u v w hadj tail ih =>
    have hadj' : faceAdjacent d (u : latticeCell d) (v : latticeCell d) := hadj
    have h0 := faceAdjacent_step_le_aux d (u : latticeCell d) (v : latticeCell d) k hadj'
    have hstep : |(((v : latticeCell d) k) - ((u : latticeCell d) k))| ≤ 1 := by
      rwa [abs_sub_comm]
    simp only [SimpleGraph.Walk.length_cons]
    push_cast
    have htri := abs_sub_le (((w : latticeCell d) k)) (((v : latticeCell d) k))
        (((u : latticeCell d) k))
    omega

lemma walk_support_length_aux (d : ℕ) (S : Finset (latticeCell d))
    {a b : ↥S} (w : (polyGraph_aux d S).Walk a b) :
    w.support.length = w.length + 1 := by
  induction w with
  | nil => simp [SimpleGraph.Walk.support_nil]
  | cons hadj tail ih => simp [SimpleGraph.Walk.support_cons, ih, SimpleGraph.Walk.length_cons]

lemma coord_lt_card_aux (d : ℕ) (S : Finset (latticeCell d))
    (hP : isPolycubeCells d S) (hC : isCanonicalCells d S)
    (x : latticeCell d) (hx : x ∈ S) (k : Fin d) :
    x k < (S.card : ℤ) := by
  obtain ⟨x0, hx0, hx0k⟩ := (hC k).1
  have hRT := hP.2 x0 hx0 x hx
  have hreach : (polyGraph_aux d S).Reachable ⟨x0, hx0⟩ ⟨x, hx⟩ := by
    rw [SimpleGraph.reachable_iff_reflTransGen]
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
    exact lift x hRT hx
  classical
  refine hreach.elim_path (fun p => by
    obtain ⟨w, hw⟩ := p
    rw [SimpleGraph.Walk.isPath_def] at hw
    have hlen_eq := walk_support_length_aux d S w
    have hnodup_le := List.Nodup.length_le_card (α := ↥S) hw
    rw [Fintype.card_coe] at hnodup_le
    have hbound := walk_coord_le_aux d S k w
    simp only at hbound
    rw [hx0k, sub_zero] at hbound
    have hlen_lt : w.length < S.card := by omega
    have hle : x k ≤ |x k| := le_abs_self _
    have hlt : (w.length : ℤ) < (S.card : ℤ) := by exact_mod_cast hlen_lt
    omega
  )

end MetaMathlibExt
end

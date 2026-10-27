import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Combinatorics.SimpleGraph.Contraction.Part3
open SimpleGraph


namespace SimpleGraph

/--
[collapseOutside_eq_none_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Contraction.lean)
-/
@[path]
lemma collapseOutside_eq_none_iff
  {D : Set V}
  {v : V} :
-- imply
  collapseOutside D v = none ↔ v ∉ D := by
-- proof
  classical
  by_cases hv : v ∈ D
  · rw [collapseOutside_of_mem D hv]
    simp [hv]
  · rw [collapseOutside_of_notMem D hv]
    simp [hv]

end SimpleGraph

namespace SimpleGraph

/--
[collapseOutside_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Contraction.lean)
-/
@[path]
lemma collapseOutside_surjective
  {D : Set V}
-- given
  (hD : Dᶜ.Nonempty) :
-- imply
  Function.Surjective (collapseOutside D) := by
-- proof
  obtain ⟨w, hw⟩ := hD
  intro z
  cases z with
  | none =>
    exact ⟨w, collapseOutside_of_notMem D hw⟩
  | some a =>
    exact ⟨a, collapseOutside_of_mem D a.property⟩

end SimpleGraph

namespace SimpleGraph

/--
[contractOutside_adj_none](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Contraction.lean)
-/
@[path]
lemma contractOutside_adj_none
  {G : SimpleGraph V}
  {D : Set V}
  {a : D} :
-- imply
  (G.contractOutside D).Adj (some a) none ↔ ∃ v ∉ D, G.Adj a v := by
-- proof
  classical
  rw [contractOutside, map_adj']
  constructor
  · rintro ⟨_, u, v, huv, hu, hv⟩
    rw [collapseOutside_eq_some_iff] at hu
    rw [collapseOutside_eq_none_iff] at hv
    exact ⟨v, hv, hu ▸ huv⟩
  · rintro ⟨v, hv, hav⟩
    refine ⟨Option.some_ne_none a, a, v, hav, ?_, ?_⟩
    · exact collapseOutside_of_mem D a.property
    · exact collapseOutside_of_notMem D hv

end SimpleGraph

namespace SimpleGraph

/--
[card_contractOutside_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Contraction.lean)
-/
@[path]
lemma card_contractOutside_lt
  [Fintype V] [Fintype ↥(Dᶜ : Set V)]
  {D : Set V} [Fintype D]
-- given
  (hD : 2 ≤ Fintype.card ↥(Dᶜ : Set V)) :
-- imply
  Fintype.card (Option D) < Fintype.card V := by
-- proof
  have hcomp := Fintype.card_compl_set D
  have hle : Fintype.card D ≤ Fintype.card V :=
    Fintype.card_le_of_injective (fun x : D ↦ (x : V)) Subtype.val_injective
  simp only [Fintype.card_option]
  omega

end SimpleGraph

/--
[map_function](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Contraction.lean)
-/
@[path]
some edges collapse to vertices. -/
private lemma Reachable.map_function {V W : Type*} {G : SimpleGraph V} {u v : V}
  (h : G.Reachable u v) (f : V → W) :
  (G.map f).Reachable (f u) (f v) := by
  rw [reachable_iff_reflTransGen] at h ⊢
  apply h.lift' f
  intro a b hab
  change Relation.ReflTransGen (G.map f).Adj (f a) (f b)
  by_cases heq : f a = f b
  · rw [heq]
  · exact Relation.ReflTransGen.single ⟨heq, a, b, hab, rfl, rfl⟩


namespace SimpleGraph

/--
[of_surjective_map_or_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Contraction.lean)
-/
@[path]
a connected graph to a connected graph. -/
private lemma Connected.of_surjective_map_or_eq {V W : Type*} {G : SimpleGraph V}
  {H : SimpleGraph W} (hG : G.Connected) (f : V → W) (hf : Function.Surjective f)
  (hadj : ∀ ⦃a b⦄, G.Adj a b → f a = f b ∨ H.Adj (f a) (f b)) : H.Connected := by
  refine { preconnected := ?_, nonempty := Nonempty.map f hG.nonempty }
  intro a b
  obtain ⟨u, rfl⟩ := hf a
  obtain ⟨v, rfl⟩ := hf b
  rw [reachable_iff_reflTransGen] at ⊢
  have huv := hG u v
  rw [reachable_iff_reflTransGen] at huv
  apply huv.lift' f
  intro y z hyz
  change Relation.ReflTransGen H.Adj (f y) (f z)
  obtain heq | h := hadj hyz
  · rw [heq]
  · exact Relation.ReflTransGen.single h

end SimpleGraph

namespace SimpleGraph

/--
[contractOutside](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Contraction.lean)
-/
@[path]
private lemma Connected.contractOutside {V : Type*} {G : SimpleGraph V} {D : Set V}
  (hG : G.Connected) (hD : Dᶜ.Nonempty) : (G.contractOutside D).Connected := by
  let f := collapseOutside D
  have hf : Function.Surjective f := collapseOutside_surjective hD
  refine { preconnected := ?_, nonempty := ⟨none⟩ }
  intro a b
  obtain ⟨u, rfl⟩ := hf a
  obtain ⟨v, rfl⟩ := hf b
  exact (hG u v).map_function f

end SimpleGraph

namespace SimpleGraph

/--
[contractOutside_delete_none](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Contraction.lean)
-/
@[path]
private lemma Connected.contractOutside_delete_none {V : Type*} {G : SimpleGraph V}
  {D : Set V} (hD : (G.induce D).Connected) :
  ((G.contractOutside D).induce
    (↑({none} : Finset (Option D)) : Set (Option D))ᶜ).Connected := by
  classical
  apply hD.map (induceContractOutsideSomeHom G D)
  rintro ⟨z, hz⟩
  cases z with
  | none => simp at hz
  | some a => exact ⟨a, rfl⟩

end SimpleGraph

namespace SimpleGraph

/--
[contractOutside_delete_some](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Contraction.lean)
-/
@[path]
the contraction also leaves it connected. -/
private lemma IsVertexConnected.contractOutside_delete_some {V : Type*} [Fintype V]
  {G : SimpleGraph V} {D : Set V} (hG : G.IsVertexConnected 2) (hD : Dᶜ.Nonempty)
  (d : D) :
  ((G.contractOutside D).induce
    (↑({some d} : Finset (Option D)) : Set (Option D))ᶜ).Connected := by
  classical
  let S : Set V := (↑({(d : V)} : Finset V) : Set V)ᶜ
  let T : Set (Option D) := (↑({some d} : Finset (Option D)) : Set (Option D))ᶜ
  let f : S → T := fun v ↦ ⟨collapseOutside D v, by
    have hne : collapseOutside D v ≠ some d := by
      intro h
      have hvd := (collapseOutside_eq_some_iff D v d).mp h
      exact v.property (by simpa [S] using hvd)
    simpa [T] using hne⟩
  have hf : Function.Surjective f := by
    rintro ⟨z, hz⟩
    cases z with
    | none =>
      obtain ⟨w, hw⟩ := hD
      have hwd : w ≠ d := fun h ↦ hw (h ▸ d.property)
      let w' : S := ⟨w, by simpa [S] using hwd⟩
      refine ⟨w', Subtype.ext ?_⟩
      exact collapseOutside_of_notMem D hw
    | some a =>
      have had : a ≠ d := by simpa [T] using hz
      have haval : (a : V) ≠ d := fun h ↦ had (Subtype.ext h)
      let a' : S := ⟨a, by simpa [S] using haval⟩
      refine ⟨a', Subtype.ext ?_⟩
      exact collapseOutside_of_mem D a.property
  apply (hG.connected_compl_singleton (by omega) d).of_surjective_map_or_eq f hf
  intro a b hab
  by_cases heq : collapseOutside D a = collapseOutside D b
  · exact Or.inl (Subtype.ext heq)
  · right
    exact map_adj_apply' (induce_adj.mp hab) heq

end SimpleGraph

/--
[collapseOutside_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Contraction.lean)
-/
@[path]
private lemma collapseOutside_of_mem_eq
  {D : Set V}
  {v : V}
-- given
  (hv : v ∈ D) :
-- imply
  collapseOutside D v = some ⟨v, hv⟩ := by
-- proof
  apply SimpleGraph.collapseOutside_of_mem D hv

/--
[collapseOutside_of_notMem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Contraction.lean)
-/
@[path]
private lemma collapseOutside_of_notMem_eq
  {D : Set V}
  {v : V}
-- given
  (hv : v ∉ D) :
-- imply
  collapseOutside D v = none := by
-- proof
  apply SimpleGraph.collapseOutside_of_notMem D hv

/--
[collapseOutside_eq_some_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Contraction.lean)
-/
@[path]
private lemma collapseOutside_eq_some_iff_eq
  {D : Set V}
  {v : V}
  {a : D} :
-- imply
  collapseOutside D v = some a ↔ v = a := by
-- proof
  apply SimpleGraph.collapseOutside_eq_some_iff D v a

/--
[contractOutside_adj_some](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Contraction.lean)
-/
@[path]
private lemma contractOutside_adj_some_eq
  {G : SimpleGraph V}
  {D : Set V}
  {a b : D} :
-- imply
  (G.contractOutside D).Adj (some a) (some b) ↔ G.Adj a b := by
-- proof
  apply SimpleGraph.contractOutside_adj_some G D a b

/--
[IsVertexConnected.contractOutside](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Contraction.lean)
-/
@[path]
private lemma IsVertexConnected_contractOutside_eq
  [Fintype V]
  {G : SimpleGraph V}
  {D : Set V} [Fintype D]
-- given
  (hG : G.IsVertexConnected 2)
  (hDcard : 1 < Fintype.card D)
  (hDconn : (G.induce D).Connected)
  (hDout : Dᶜ.Nonempty) :
-- imply
  (G.contractOutside D).IsVertexConnected 2 := by
-- proof
  apply SimpleGraph.IsVertexConnected.contractOutside hG hDcard hDconn hDout


-- created on 2026-10-20
-- updated on 2026-10-26

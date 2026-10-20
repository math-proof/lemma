/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Contraction.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import sympy.atlas.Combinatorics.SimpleGraph.VertexConnectivity
/-!
# Contracting the complement of a vertex set

This file contracts every vertex outside a set to one new vertex. The construction is used by
the induction in Fleischner's theorem.
-/

namespace SimpleGraph

/-- A reachable pair remains reachable after mapping a graph by an arbitrary function, even when
some edges collapse to vertices. -/
private theorem Reachable.map_function {V W : Type*} {G : SimpleGraph V} {u v : V}
    (h : G.Reachable u v) (f : V → W) :
    (G.map f).Reachable (f u) (f v) := by
  rw [reachable_iff_reflTransGen] at h ⊢
  apply h.lift' f
  intro a b hab
  change Relation.ReflTransGen (G.map f).Adj (f a) (f b)
  by_cases heq : f a = f b
  · rw [heq]
  · exact Relation.ReflTransGen.single ⟨heq, a, b, hab, rfl, rfl⟩

/-- A surjective vertex map that sends every edge to an edge or collapses it to one vertex sends
a connected graph to a connected graph. -/
private theorem Connected.of_surjective_map_or_eq {V W : Type*} {G : SimpleGraph V}
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
  rcases hadj hyz with heq | h
  · rw [heq]
  · exact Relation.ReflTransGen.single h

/-- Send vertices in `D` to their subtype copy and every other vertex to `none`. -/
noncomputable def collapseOutside {V : Type*} (D : Set V) : V → Option D := by
  classical
  exact fun v ↦ if hv : v ∈ D then some ⟨v, hv⟩ else none

/-- A vertex in `D` survives contraction as its subtype copy. -/
@[simp]
theorem collapseOutside_of_mem {V : Type*} (D : Set V) {v : V} (hv : v ∈ D) :
    collapseOutside D v = some ⟨v, hv⟩ := by
  classical
  simp [collapseOutside, hv]

/-- A vertex outside `D` is sent to the contraction vertex. -/
@[simp]
theorem collapseOutside_of_notMem {V : Type*} (D : Set V) {v : V} (hv : v ∉ D) :
    collapseOutside D v = none := by
  classical
  simp [collapseOutside, hv]

/-- Characterization of the vertices that map to a surviving subtype vertex. -/
@[simp]
theorem collapseOutside_eq_some_iff {V : Type*} (D : Set V) (v : V) (a : D) :
    collapseOutside D v = some a ↔ v = a := by
  classical
  by_cases hv : v ∈ D
  · rw [collapseOutside_of_mem D hv]
    simp only [Option.some.injEq]
    constructor
    · exact fun h ↦ congrArg Subtype.val h
    · intro h
      apply Subtype.ext
      exact h
  · rw [collapseOutside_of_notMem D hv]
    constructor
    · intro h
      contradiction
    · intro h
      exfalso
      apply hv
      rw [h]
      exact a.property

/-- Characterization of the vertices sent to the contraction vertex. -/
@[simp]
theorem collapseOutside_eq_none_iff {V : Type*} (D : Set V) (v : V) :
    collapseOutside D v = none ↔ v ∉ D := by
  classical
  by_cases hv : v ∈ D
  · rw [collapseOutside_of_mem D hv]
    simp [hv]
  · rw [collapseOutside_of_notMem D hv]
    simp [hv]

/-- The collapse map is onto when there is a vertex outside the retained set. -/
theorem collapseOutside_surjective {V : Type*} {D : Set V} (hD : Dᶜ.Nonempty) :
    Function.Surjective (collapseOutside D) := by
  obtain ⟨w, hw⟩ := hD
  intro z
  cases z with
  | none =>
      exact ⟨w, collapseOutside_of_notMem D hw⟩
  | some a =>
      exact ⟨a, collapseOutside_of_mem D a.property⟩

/-- Contract the complement of `D` to one vertex. -/
noncomputable def contractOutside {V : Type*} (G : SimpleGraph V) (D : Set V) :
    SimpleGraph (Option D) :=
  G.map (collapseOutside D)

/-- Adjacency between surviving vertices is unchanged by contraction. -/
@[simp]
theorem contractOutside_adj_some {V : Type*} (G : SimpleGraph V) (D : Set V)
    (a b : D) :
    (G.contractOutside D).Adj (some a) (some b) ↔ G.Adj a b := by
  classical
  rw [contractOutside, map_adj']
  constructor
  · rintro ⟨_, u, v, huv, hu, hv⟩
    rw [collapseOutside_eq_some_iff] at hu hv
    simpa [hu, hv] using huv
  · intro hab
    refine ⟨?_, a, b, hab, ?_, ?_⟩
    · intro h
      exact G.ne_of_adj hab (congrArg Subtype.val (Option.some.inj h))
    · exact collapseOutside_of_mem D a.property
    · exact collapseOutside_of_mem D b.property

/-- A surviving vertex is adjacent to the contraction vertex exactly when it had a neighbor
outside the contracted set. -/
@[simp]
theorem contractOutside_adj_none {V : Type*} (G : SimpleGraph V) (D : Set V)
    (a : D) :
    (G.contractOutside D).Adj (some a) none ↔ ∃ v ∉ D, G.Adj a v := by
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

/-- Contracting a nonempty complement preserves connectedness. -/
private theorem Connected.contractOutside {V : Type*} {G : SimpleGraph V} {D : Set V}
    (hG : G.Connected) (hD : Dᶜ.Nonempty) : (G.contractOutside D).Connected := by
  let f := collapseOutside D
  have hf : Function.Surjective f := collapseOutside_surjective hD
  refine { preconnected := ?_, nonempty := ⟨none⟩ }
  intro a b
  obtain ⟨u, rfl⟩ := hf a
  obtain ⟨v, rfl⟩ := hf b
  exact (hG u v).map_function f

private noncomputable def induceContractOutsideSomeHom {V : Type*}
    (G : SimpleGraph V) (D : Set V) :
    G.induce D →g
      (G.contractOutside D).induce
        (↑({none} : Finset (Option D)) : Set (Option D))ᶜ where
  toFun a := ⟨some a, by simp⟩
  map_rel' := by
    intro a b hab
    exact contractOutside_adj_some G D a b |>.mpr (induce_adj.mp hab)

/-- Deleting the contraction vertex leaves the original induced graph on the retained set. -/
private theorem Connected.contractOutside_delete_none {V : Type*} {G : SimpleGraph V}
    {D : Set V} (hD : (G.induce D).Connected) :
    ((G.contractOutside D).induce
      (↑({none} : Finset (Option D)) : Set (Option D))ᶜ).Connected := by
  classical
  apply hD.map (induceContractOutsideSomeHom G D)
  rintro ⟨z, hz⟩
  cases z with
  | none => simp at hz
  | some a => exact ⟨a, rfl⟩

/-- If deleting one vertex from `G` leaves it connected, then deleting a surviving vertex from
the contraction also leaves it connected. -/
private theorem IsVertexConnected.contractOutside_delete_some {V : Type*} [Fintype V]
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

/-- Contracting the complement of a connected set with at least two vertices in a
2-vertex-connected graph produces another 2-vertex-connected graph. -/
theorem IsVertexConnected.contractOutside {V : Type*} [Fintype V]
    {G : SimpleGraph V} {D : Set V} [Fintype D] (hG : G.IsVertexConnected 2)
    (hDcard : 1 < Fintype.card D) (hDconn : (G.induce D).Connected)
    (hDout : Dᶜ.Nonempty) : (G.contractOutside D).IsVertexConnected 2 := by
  classical
  rw [isVertexConnected_two_iff]
  refine ⟨?_, hG.connected (by omega) |>.contractOutside hDout, ?_⟩
  · simp only [Fintype.card_option]
    omega
  · intro z
    cases z with
    | none => exact hDconn.contractOutside_delete_none
    | some d => exact hG.contractOutside_delete_some hDout d

/-- If at least two vertices are contracted, the contraction has strictly fewer vertices. -/
theorem card_contractOutside_lt {V : Type*} [Fintype V] (D : Set V)
    [Fintype D] [Fintype ↥(Dᶜ : Set V)] (hD : 2 ≤ Fintype.card ↥(Dᶜ : Set V)) :
    Fintype.card (Option D) < Fintype.card V := by
  have hcomp := Fintype.card_compl_set D
  have hle : Fintype.card D ≤ Fintype.card V :=
    Fintype.card_le_of_injective (fun x : D ↦ (x : V)) Subtype.val_injective
  simp only [Fintype.card_option]
  omega

end SimpleGraph

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Coloring/Vertex.lean -/

/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import sympy.atlas.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.NNRat.Floor
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Set.Card

variable {V α : Type*} {G : SimpleGraph V} {n : ℕ}

namespace SimpleGraph

@[inherit_doc] scoped notation "χ(" G ")" => chromaticNumber G

lemma lt_chromaticNumber_iff_not_colorable : n < G.chromaticNumber ↔ ¬ G.Colorable n := by
  rw [← chromaticNumber_le_iff_colorable, not_le]

lemma le_chromaticNumber_iff_not_colorable (hn : n ≠ 0) :
    n ≤ G.chromaticNumber ↔ ¬ G.Colorable (n - 1) := by
  let n + 1 := n; simp [ENat.add_one_le_iff, lt_chromaticNumber_iff_not_colorable]

lemma card_div_indepNum_le_chromaticNumber : ⌈(Nat.card V / α(G) : ℚ≥0)⌉₊ ≤ G.chromaticNumber := by
  cases finite_or_infinite V
  swap; · simp
  cases nonempty_fintype V
  simp only [Nat.card_eq_fintype_card, le_chromaticNumber_iff_coloring, Nat.ceil_le]
  refine fun m c ↦ div_le_of_le_mul₀ (by simp) (by simp) ?_
  norm_cast
  rw [← mul_one (Fintype.card V), ← Fintype.card_fin m]
  refine Finset.card_mul_le_card_mul (c · = ·)
    (by simp [Finset.bipartiteAbove, Finset.filter_nonempty_iff])
    fun b _ ↦ IsIndepSet.card_le_indepNum ?_
  simpa [IsIndepSet, Set.Pairwise, Coloring.colorClass] using
    fun x hx y hy _ ↦ c.not_adj_of_mem_colorClass hx hy

variable (G) in
/-- A set of edges is critical if deleting them reduces the chromatic number. -/
def IsCriticalEdges (edges : Set (Sym2 V)) : Prop :=
  (G.deleteEdges edges).chromaticNumber < G.chromaticNumber

variable (G) in
/-- An edge is critical if deleting it reduces the chromatic number. -/
def IsCriticalEdge (e : Sym2 V) : Prop := G.IsCriticalEdges ({e} : Set (Sym2 V))

/--
A set of vertices is critical if deleting them reduces the chromatic number.
-/
def Subgraph.IsCriticalVerts (verts : Set V) (G' : G.Subgraph) : Prop :=
  (G'.deleteVerts verts).coe.chromaticNumber < G'.coe.chromaticNumber

/--
A vertex is critical if deleting it reduces the chromatic number.
-/
def Subgraph.IsCriticalVertex (v : V) (G' : G.Subgraph) : Prop := G'.IsCriticalVerts {v}

variable (G)

/--
A graph `G` is `k`-critical (or vertex-critical) if its chromatic number is `k`,
and deleting any single vertex reduces the chromatic number.
-/
def IsCritical (k : ℕ) : Prop := G.chromaticNumber = k ∧ ∀ v, (⊤ : G.Subgraph).IsCriticalVertex v

theorem not_isCritical_of_fintype_lt [Fintype V] (k : ℕ) (hk : Fintype.card V < k) :
   ¬G.IsCritical k := by
  simp only [IsCritical, not_and, not_forall]
  intro h
  have := h ▸ SimpleGraph.chromaticNumber_le_iff_colorable.2 G.colorable_of_fintype
  simp at this
  grind

open SimpleGraph

set_option backward.isDefEq.respectTransparency false in
theorem colorable_iff_induce_eq_bot (G : SimpleGraph V) (n : ℕ) :
    G.Colorable n ↔ ∃ coloring : V → Fin n, ∀ i, G.induce {v | coloring v = i} = ⊥ := by
  refine ⟨fun ⟨a, h⟩ ↦ ⟨a, fun i ↦ ?_⟩, fun ⟨w, h⟩ ↦ ⟨w, @fun a b h_adj ↦ ?_⟩⟩
  · rw [SimpleGraph.eq_bot_iff_forall_not_adj]
    rintro ⟨u, huv⟩ ⟨v, rfl⟩ huv'
    exact (h huv').ne huv
  specialize h (w a)
  contrapose h
  intro hG
  have : ¬ ((SimpleGraph.induce {v | w v = w a} G).Adj ⟨a, by rfl⟩ ⟨b, by simp_all⟩) :=
    hG ▸ fun a ↦ a
  exact this h_adj

/--
`G.Cocolorable n` means that the vertices of `G` can be colored with `n` colors so that each
color class induces either an independent set or a complete graph.
-/
def Cocolorable (G : SimpleGraph V) (n : ℕ) : Prop := ∃ coloring : V → Fin n,
  ∀ i, G.induce {v | coloring v = i} = ⊥ ∨ G.induce {v | coloring v = i} = ⊤

/-- Every proper coloring is a cocoloring: color classes inducing `⊥` also satisfy the
`⊥ ∨ ⊤` disjunction. -/
theorem Colorable.cocolorable {n : ℕ} (hc : G.Colorable n) : G.Cocolorable n := by
  obtain ⟨coloring, hcol⟩ := (colorable_iff_induce_eq_bot G n).mp hc
  exact ⟨coloring, fun i => Or.inl (hcol i)⟩

/-- Every finite graph is cocolorable, via its tautological finite coloring. -/
theorem cocolorable_of_fintype [Fintype V] (G : SimpleGraph V) :
    G.Cocolorable (Fintype.card V) :=
  (colorable_of_fintype G).cocolorable

/--
The cochromatic number of a graph is the minimal number of colors needed to color its vertices
so that each color class induces either an independent set or a complete graph.
This is `⊤` (infinity) iff `G` isn't cocolorable with finitely many colors.

If `G` is cocolorable, then `ENat.toNat G.cochromaticNumber` is the `ℕ`-valued cochromatic number.
-/
noncomputable def cochromaticNumber (G : SimpleGraph V) : ℕ∞ := ⨅ n ∈ Set.ofPred G.Cocolorable,
  (n : ℕ∞)

/-- Finite cocolorability description of the cochromatic number, mirroring
`Colorable.chromaticNumber_eq_sInf`. -/
theorem Cocolorable.cochromaticNumber_eq_sInf {n : ℕ} (h : G.Cocolorable n) :
    G.cochromaticNumber = sInf {n' : ℕ | G.Cocolorable n'} := by
  rw [ENat.natCast_sInf, cochromaticNumber]
  exact ⟨_, h⟩

/-- For a finite vertex type, `toNat` of the `ℕ∞` cochromatic number is the natural-valued
minimum of admissible color counts. -/
theorem cochromaticNumber_toNat_eq_sInf [Fintype V] (G : SimpleGraph V) :
    G.cochromaticNumber.toNat = sInf {n : ℕ | G.Cocolorable n} := by
  rw [(cocolorable_of_fintype G).cochromaticNumber_eq_sInf, ENat.toNat_natCast]

/-- The chromatic cardinal is the minimal number of colors need to color it. In contrast to
`chromaticNumber`, which assigns `⊤ : ℕ∞` to all non-finitely colorable graphs, this definition
returns a `Cardinal` and can therefore distinguish between different infinite chromatic numbers. -/
noncomputable def chromaticCardinal.{u} {V : Type u} (G : SimpleGraph V) : Cardinal :=
  sInf {κ : Cardinal | ∃ (C : Type u) (_ : Cardinal.mk C = κ), Nonempty (G.Coloring C)}

/-- The maximum size of the union of k finite independent sets. -/
noncomputable def indepNumK (G : SimpleGraph V) [Fintype V] (k : ℕ) : ℕ :=
  sSup {n | ∃ f : Fin k → Set V, (∀ i, G.IsIndepSet (f i)) ∧ (⋃ i, f i).ncard = n}

theorem indepNumK_le_card [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    indepNumK G k ≤ Fintype.card V := by
  refine csSup_le ⟨0, fun _ => ∅, fun _ _ hx => False.elim hx, by simp⟩ ?_
  rintro n ⟨f, _, rfl⟩
  simpa using Set.ncard_le_card (⋃ i, f i)

/-- A finite graph is CDS-colorable if it has a proper coloring
by natural numbers such that for all `k > 0`, the number of
vertices with color `< k` equals the maximum size of
the union of `k` independent sets. -/
def CDSColorable [Fintype α] (G : SimpleGraph α) : Prop :=
    ∃ (C : G.Coloring Nat), ∀ k : Nat,
   ∑ i < k, (C.colorClass i).ncard = indepNumK G k

/-- A homomorphism `f : H →g G` is rainbow for an edge labeling `c` of `G` if it maps distinct
edges of `H` to edges of `G` with distinct labels. -/
def IsRainbow {α V K : Type*} {H : SimpleGraph α} {G : SimpleGraph V} (f : H →g G)
    (c : G.EdgeLabeling K) : Prop :=
  Function.Injective (c.pullback f)

/--
The anti-Ramsey number $\mathrm{AR}(n, H)$: the maximum number of colors in an edge coloring of
$K_n$ (that is, a labeling of the edges of $K_n$ using every color) that contains no rainbow copy
of $H$, i.e. no injective homomorphism (copy) of $H$ whose edges all receive different colors.
-/
noncomputable def antiRamseyNum {α : Type*} [Fintype α] (H : SimpleGraph α) (n : ℕ) : ℕ :=
  sSup {k | ∃ c : TopEdgeLabeling (Fin n) (Fin k), Function.Surjective c ∧
    ∀ f : H.Copy ⊤, ¬IsRainbow f.toHom c}

end SimpleGraph

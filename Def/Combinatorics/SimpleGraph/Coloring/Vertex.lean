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

import Def.Combinatorics.SimpleGraph.Clique
import Lemma.SimpleGraph.Clique
import Mathlib.Data.NNRat.Floor
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Set.Card
variable {V α : Type*} {G : SimpleGraph V} {n : ℕ}


namespace SimpleGraph

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

/--
`G.Cocolorable n` means that the vertices of `G` can be colored with `n` colors so that each
color class induces either an independent set or a complete graph.
-/
def Cocolorable (G : SimpleGraph V) (n : ℕ) : Prop := ∃ coloring : V → Fin n,
  ∀ i, G.induce {v | coloring v = i} = ⊥ ∨ G.induce {v | coloring v = i} = ⊤

/--
The cochromatic number of a graph is the minimal number of colors needed to color its vertices
so that each color class induces either an independent set or a complete graph.
This is `⊤` (infinity) iff `G` isn't cocolorable with finitely many colors.

If `G` is cocolorable, then `ENat.toNat G.cochromaticNumber` is the `ℕ`-valued cochromatic number.
-/
noncomputable def cochromaticNumber (G : SimpleGraph V) : ℕ∞ := ⨅ n ∈ Set.ofPred G.Cocolorable,
  (n : ℕ∞)

/-- The chromatic cardinal is the minimal number of colors need to color it. In contrast to
`chromaticNumber`, which assigns `⊤ : ℕ∞` to all non-finitely colorable graphs, this definition
returns a `Cardinal` and can therefore distinguish between different infinite chromatic numbers. -/
noncomputable def chromaticCardinal.{u} {V : Type u} (G : SimpleGraph V) : Cardinal :=
  sInf {κ : Cardinal | ∃ (C : Type u) (_ : Cardinal.mk C = κ), Nonempty (G.Coloring C)}

/-- The maximum size of the union of k finite independent sets. -/
noncomputable def indepNumK (G : SimpleGraph V) [Fintype V] (k : ℕ) : ℕ :=
  sSup {n | ∃ f : Fin k → Set V, (∀ i, G.IsIndepSet (f i)) ∧ (⋃ i, f i).ncard = n}

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

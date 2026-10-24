/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Brooks.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

section
namespace MathlibExt.Combinatorics.SimpleGraph.BrooksWanted

/-!
# Brooks' theorem
-/

open Finset

private def IsProperOn {V : Type*} {k : ℕ} (G : SimpleGraph V) (f : V → Fin k) (W : Finset V) :
    Prop :=
  ∀ a ∈ W, ∀ b ∈ W, G.Adj a b → f a ≠ f b

/-- `LinkedOn G W` means every nontrivial cut of `W` is crossed by an edge. -/
private def LinkedOn {V : Type*} (G : SimpleGraph V) (W : Finset V) : Prop :=
  ∀ S : Finset V, S ⊆ W → S.Nonempty →
    (∃ t ∈ W, t ∉ S) → ∃ s ∈ S, ∃ t ∈ W, t ∉ S ∧ G.Adj s t
end MathlibExt.Combinatorics.SimpleGraph.BrooksWanted
end

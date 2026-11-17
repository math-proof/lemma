/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Brooks.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

@[expose] public section

/-!
# Brooks' theorem
-/


section

namespace MathlibExt.Combinatorics.SimpleGraph.BrooksWanted

open Finset

def IsProperOn {V : Type*} {k : ℕ} (G : SimpleGraph V) (f : V → Fin k) (W : Finset V) :
    Prop :=
  ∀ a ∈ W, ∀ b ∈ W, G.Adj a b → f a ≠ f b

/-- `LinkedOn G W` means every nontrivial cut of `W` is crossed by an edge. -/
def LinkedOn {V : Type*} (G : SimpleGraph V) (W : Finset V) : Prop :=
  ∀ S : Finset V, S ⊆ W → S.Nonempty →
    (∃ t ∈ W, t ∉ S) → ∃ s ∈ S, ∃ t ∈ W, t ∉ S ∧ G.Adj s t

end MathlibExt.Combinatorics.SimpleGraph.BrooksWanted
end

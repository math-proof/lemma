/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/HajnalSzemeredi.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Relation


namespace MathlibExt.Combinatorics.SimpleGraph.HajnalSzemerediWanted

/-!
# Hajnal–Szemerédi equitable coloring — private development

Short proof of Kierstead–Kostochka (2008). All helpers are private with `hs`
prefix. The public declarations are `exists_equitable_coloring_of_maxDegree_lt`,
which needs no `DecidableEq V` instance, and the Wanted statement
`hajnal_szemeredi_equitable_coloring`, a wrapper around it.
-/

/-- Color class: vertices of `U` colored `c` by `f`. -/
def hsCls {V C : Type*} [DecidableEq V] [DecidableEq C]
    (U : Finset V) (f : V → C) (c : C) : Finset V :=
  U.filter fun u => f u = c

/-- Neighbours of `v` inside `U`. -/
def hsNbr {V : Type*} [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (v : V) : Finset V :=
  U.filter fun u => H.Adj v u

/-- Every vertex of `U` gets a color in `K`. -/
def hsMaps {V C : Type*} [DecidableEq V] [DecidableEq C]
    (U : Finset V) (K : Finset C) (f : V → C) : Prop :=
  ∀ u ∈ U, f u ∈ K

/-- `f` is proper on `U`: adjacent vertices get different colors. -/
def hsProper {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) (U : Finset V) (f : V → C) : Prop :=
  ∀ u ∈ U, ∀ v ∈ U, H.Adj u v → f u ≠ f v

/-- Every vertex of `U` has fewer than `K.card` neighbours in `U`. -/
def hsDegLt {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) : Prop :=
  ∀ v ∈ U, (hsNbr H U v).card < K.card

/-- Every color of `K` is used exactly `m` times on `U`. -/
def hsEquitable {V C : Type*} [DecidableEq V] [DecidableEq C]
    (U : Finset V) (K : Finset C) (f : V → C) (m : ℕ) : Prop :=
  ∀ c ∈ K, (hsCls U f c).card = m

/-- Nearly equitable: class `α₀` is one short, class `β₀` has one extra. -/
def hsNearly {V C : Type*} [DecidableEq V] [DecidableEq C]
    (U : Finset V) (K : Finset C) (f : V → C) (m : ℕ) (α₀ β₀ : C) : Prop :=
  α₀ ∈ K ∧ β₀ ∈ K ∧ α₀ ≠ β₀ ∧ (hsCls U f α₀).card + 1 = m ∧
    (hsCls U f β₀).card = m + 1 ∧
    ∀ c ∈ K, c ≠ α₀ → c ≠ β₀ → (hsCls U f c).card = m

/-- Auxiliary digraph on colors: `σ → τ` when some vertex of class `σ`
has no neighbour in class `τ`. -/
def hsEdge {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) (U : Finset V) (K : Finset C)
    (f : V → C) (σ τ : C) : Prop :=
  σ ∈ K ∧ τ ∈ K ∧ σ ≠ τ ∧
    ∃ x ∈ U, f x = σ ∧ ∀ y ∈ U, f y = τ → ¬ H.Adj x y

/-- The avoiding relation: steps of `E` that neither start nor end at `ν`. -/
def hsAvoid {C : Type*} (E : C → C → Prop) (ν : C) : C → C → Prop :=
  fun σ τ => E σ τ ∧ σ ≠ ν ∧ τ ≠ ν

/-- Colors of `K` that can reach `α₀` in the auxiliary digraph. -/
noncomputable def hsReachSet {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (α₀ : C) : Finset C :=
  @Finset.filter C (fun σ => Relation.ReflTransGen (hsEdge H U K f) σ α₀)
    (fun _ => Classical.propDecidable _) K

/-- Terminal colors: those in the reach set whose every fellow member reaches
`α₀` even while avoiding them. -/
noncomputable def hsTerminal {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (α₀ : C) : Finset C :=
  @Finset.filter C
    (fun σ => ∀ γ ∈ hsReachSet H U K f α₀, γ ≠ σ →
      Relation.ReflTransGen (hsAvoid (hsEdge H U K f) σ) γ α₀)
    (fun _ => Classical.propDecidable _) (hsReachSet H U K f α₀)

/-- Auxiliary: colors of `𝒜` reaching `α₀` while avoiding `ν`. -/
noncomputable def hsDset {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (α₀ ν : C) : Finset C :=
  @Finset.filter C
    (fun c => c ≠ ν ∧ Relation.ReflTransGen (hsAvoid (hsEdge H U K f) ν) c α₀)
    (fun _ => Classical.propDecidable _) (hsReachSet H U K f α₀)

/-- Auxiliary: the solo vertices in the class of `τ`. -/
noncomputable def hsSol {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (α₀ τ : C) : Finset V :=
  @Finset.filter V
    (fun w => ∃ z ∈ U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀,
      H.Adj z w ∧ ∀ v ∈ hsCls U f (f w), H.Adj z v → v = w)
    (fun _ => Classical.propDecidable _) (hsCls U f τ)

/-- Auxiliary: vertices of `B` adjacent to some solo vertex. -/
noncomputable def hsN {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (α₀ : C)
    (Sol : Finset V) : Finset V :=
  @Finset.filter V (fun z => ∃ w ∈ Sol, H.Adj z w)
    (fun _ => Classical.propDecidable _)
    (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀)

/-- Auxiliary: the solo partners of `z` (in `A'`). -/
noncomputable def hsSoloOf {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (α₀ : C) (z : V) : Finset V :=
  @Finset.filter V
    (fun w => H.Adj z w ∧ ∀ v ∈ hsCls U f (f w), H.Adj z v → v = w)
    (fun _ => Classical.propDecidable _)
    (U.filter fun u => f u ∈ hsTerminal H U K f α₀)

/-- Auxiliary: pairs `(z, w)` with `z ∈ I` and `w` a solo partner of `z`. -/
noncomputable def hsP {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (α₀ : C)
    (I : Finset V) : Finset (V × V) :=
  @Finset.filter (V × V)
    (fun p => p.2 ∈ hsSoloOf H U K f α₀ p.1)
    (fun _ => Classical.propDecidable _)
    (I ×ˢ (U.filter fun u => f u ∈ hsTerminal H U K f α₀))

/-- Auxiliary: the spanning subgraph of `G'` on the vertices of `S`. -/
def hsSub {V' : Type*} [DecidableEq V'] (G' : SimpleGraph V')
    (S : Finset V') : SimpleGraph V' where
  Adj u v := G'.Adj u v ∧ u ∈ S ∧ v ∈ S
  symm := ⟨fun _ _ h => ⟨G'.adj_symm h.1, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => G'.irrefl h.1⟩

end MathlibExt.Combinatorics.SimpleGraph.HajnalSzemerediWanted

import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Combinatorics.EndpointMapMultigraph
open EndpointMapMultigraph


namespace EndpointMapMultigraph

/--
[incident_swap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/EndpointMapMultigraph.lean)
-/
@[path]
lemma incident_swap
  {end₁ end₂ : E → V}
  {v : V}
  {F : Finset E} :
-- imply
  incident end₂ end₁ v F = incident end₁ end₂ v F := by
-- proof
  classical
  ext e
  simp [or_comm]

end EndpointMapMultigraph

namespace EndpointMapMultigraph

/--
[degreeWithin_swap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/EndpointMapMultigraph.lean)
-/
@[path]
lemma degreeWithin_swap
  {end₁ end₂ : E → V}
  {F : Finset E}
  {v : V} :
-- imply
  degreeWithin end₂ end₁ F v = degreeWithin end₁ end₂ F v := by
-- proof
  classical
  simp [degreeWithin, Nat.add_comm]
@[simp] theorem mem_support {V E : Type*} (end₁ end₂ : E → V) (F : Finset E) (v : V) :
  v ∈ support end₁ end₂ F ↔ ∃ e ∈ F, end₁ e = v ∨ end₂ e = v := by
  classical
  simp [support]

end EndpointMapMultigraph

namespace EndpointMapMultigraph

/--
[support_swap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/EndpointMapMultigraph.lean)
-/
@[path]
lemma support_swap
  {end₁ end₂ : E → V}
  {F : Finset E} :
-- imply
  support end₂ end₁ F = support end₁ end₂ F := by
-- proof
  ext v
  simp [or_comm]

end EndpointMapMultigraph

namespace EndpointMapMultigraph

/--
[adjacentUsing_symm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/EndpointMapMultigraph.lean)
-/
@[path]
lemma adjacentUsing_symm
  {end₁ end₂ : E → V}
  {F : Finset E}
  {u v : V} :
-- imply
  AdjacentUsing end₁ end₂ F u v ↔ AdjacentUsing end₁ end₂ F v u := by
-- proof
  classical
  simp [AdjacentUsing, and_comm, or_comm]

end EndpointMapMultigraph

namespace EndpointMapMultigraph

/--
[adjacentUsing_swap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/EndpointMapMultigraph.lean)
-/
@[path]
lemma adjacentUsing_swap
  {end₁ end₂ : E → V}
  {F : Finset E}
  {u v : V} :
-- imply
  AdjacentUsing end₂ end₁ F u v ↔ AdjacentUsing end₁ end₂ F u v := by
-- proof
  classical
  simp [AdjacentUsing, and_comm, or_comm]

end EndpointMapMultigraph

namespace EndpointMapMultigraph

/--
[isConnectedOnSupport_swap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/EndpointMapMultigraph.lean)
-/
@[path]
lemma isConnectedOnSupport_swap
  {end₁ end₂ : E → V}
  {F : Finset E} :
-- imply
  IsConnectedOnSupport end₂ end₁ F ↔ IsConnectedOnSupport end₁ end₂ F := by
-- proof
  have hadj : AdjacentUsing end₂ end₁ F = AdjacentUsing end₁ end₂ F := by
    funext u v
    exact propext (adjacentUsing_swap end₁ end₂ F u v)
  rw [IsConnectedOnSupport, IsConnectedOnSupport, support_swap, hadj]

end EndpointMapMultigraph

namespace EndpointMapMultigraph

/--
[isCircuit_swap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/EndpointMapMultigraph.lean)
-/
@[path]
lemma isCircuit_swap
  {end₁ end₂ : E → V}
  {F : Finset E} :
-- imply
  IsCircuit end₂ end₁ F ↔ IsCircuit end₁ end₂ F := by
-- proof
  simp only [IsCircuit, support_swap, degreeWithin_swap, isConnectedOnSupport_swap]

end EndpointMapMultigraph

namespace EndpointMapMultigraph

/--
[degreeWithin_eq_card_incident_of_loopless](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/EndpointMapMultigraph.lean)
-/
@[path]
lemma degreeWithin_eq_card_incident_of_loopless
  {end₁ end₂ : E → V}
  {F : Finset E}
  {v : V}
-- given
  (h : ∀ e ∈ F, end₁ e ≠ end₂ e) :
-- imply
  degreeWithin end₁ end₂ F v = (incident end₁ end₂ v F).card := by
-- proof
  classical
  let F₁ := F.filter (fun e => end₁ e = v)
  let F₂ := F.filter (fun e => end₂ e = v)
  have hdisjoint : Disjoint F₁ F₂ := by
    rw [Finset.disjoint_left]
    intro e he₁ he₂
    simp only [F₁, F₂, Finset.mem_filter] at he₁ he₂
    exact h e he₁.1 (he₁.2.trans he₂.2.symm)
  have hunion : F₁ ∪ F₂ = incident end₁ end₂ v F := by
    ext e
    simp only [F₁, F₂, incident, Finset.mem_union, Finset.mem_filter]
    tauto
  rw [degreeWithin]
  change F₁.card + F₂.card = _
  rw [← Finset.card_union_of_disjoint hdisjoint, hunion]
@[simp] theorem mem_cut {V E : Type*} [Fintype E] (end₁ end₂ : E → V)
  (X : Finset V) (e : E) :
  e ∈ cut end₁ end₂ X ↔ (end₁ e ∈ X) ≠ (end₂ e ∈ X) := by
  classical
  simp [cut]

end EndpointMapMultigraph

namespace EndpointMapMultigraph

/--
[cut_swap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/EndpointMapMultigraph.lean)
-/
@[path]
lemma cut_swap
  [Fintype E]
  {end₁ end₂ : E → V}
  {X : Finset V} :
-- imply
  cut end₂ end₁ X = cut end₁ end₂ X := by
-- proof
  ext e
  simp only [mem_cut]
  exact ne_comm

end EndpointMapMultigraph

namespace EndpointMapMultigraph

/--
[degreeWithin_singleton_loop](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/EndpointMapMultigraph.lean)
-/
@[path]
lemma degreeWithin_singleton_loop
  {end₁ end₂ : E → V}
  {e : E}
-- given
  (h : end₁ e = end₂ e) :
-- imply
  degreeWithin end₁ end₂ {e} (end₁ e) = 2 := by
-- proof
  classical
  rw [degreeWithin, Finset.filter_singleton, Finset.filter_singleton]
  simp [h.symm]

end EndpointMapMultigraph

namespace EndpointMapMultigraph

/--
[loop_not_mem_cut](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/EndpointMapMultigraph.lean)
-/
@[path]
lemma loop_not_mem_cut
  [Fintype E]
  {end₁ end₂ : E → V}
  {X : Finset V}
  {e : E}
-- given
  (h : end₁ e = end₂ e) :
-- imply
  e ∉ cut end₁ end₂ X := by
-- proof
  classical
  simp [h]
@[simp] theorem isConnectedOnSupport_empty {V E : Type*} (end₁ end₂ : E → V) :
  IsConnectedOnSupport end₁ end₂ (∅ : Finset E) := by
  simp [IsConnectedOnSupport]
@[simp] theorem not_isCircuit_empty {V E : Type*} (end₁ end₂ : E → V) :
  ¬IsCircuit end₁ end₂ (∅ : Finset E) := by
  simp [IsCircuit]

end EndpointMapMultigraph

/--
[mem_incident](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/EndpointMapMultigraph.lean)
-/
@[path]
private lemma mem_incident_eq
  {end₁ end₂ : E → V}
  {v : V}
  {F : Finset E}
  {e : E} :
-- imply
  e ∈ incident end₁ end₂ v F ↔ e ∈ F ∧ (end₁ e = v ∨ end₂ e = v) := by
-- proof
  apply EndpointMapMultigraph.mem_incident end₁ end₂ v F e

/--
[mem_support](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/EndpointMapMultigraph.lean)
-/
@[path]
private lemma mem_support_eq
  {end₁ end₂ : E → V}
  {F : Finset E}
  {v : V} :
-- imply
  v ∈ support end₁ end₂ F ↔ ∃ e ∈ F, end₁ e = v ∨ end₂ e = v := by
-- proof
  apply EndpointMapMultigraph.mem_support end₁ end₂ F v

/--
[mem_cut](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/EndpointMapMultigraph.lean)
-/
@[path]
private lemma mem_cut_eq
  [Fintype E]
  {end₁ end₂ : E → V}
  {X : Finset V}
  {e : E} :
-- imply
  e ∈ cut end₁ end₂ X ↔ (end₁ e ∈ X) ≠ (end₂ e ∈ X) := by
-- proof
  apply EndpointMapMultigraph.mem_cut end₁ end₂ X e

/--
[isConnectedOnSupport_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/EndpointMapMultigraph.lean)
-/
@[path]
private lemma isConnectedOnSupport_empty_eq
  {end₁ end₂ : E → V} :
-- imply
  IsConnectedOnSupport end₁ end₂ (∅ : Finset E) := by
-- proof
  apply EndpointMapMultigraph.isConnectedOnSupport_empty end₁ end₂

/--
[not_isCircuit_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/EndpointMapMultigraph.lean)
-/
@[path]
private lemma not_isCircuit_empty_eq
  {end₁ end₂ : E → V} :
-- imply
  ¬IsCircuit end₁ end₂ (∅ : Finset E) := by
-- proof
  apply EndpointMapMultigraph.not_isCircuit_empty end₁ end₂


-- created on 2026-10-20
-- updated on 2026-10-26

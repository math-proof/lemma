import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.EndpointMapMultigraph
open EndpointMapMultigraph


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
[incident_swap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/EndpointMapMultigraph.lean)
-/
@[path]
private lemma incident_swap_eq
  {end₁ end₂ : E → V}
  {v : V}
  {F : Finset E} :
-- imply
  incident end₂ end₁ v F = incident end₁ end₂ v F := by
-- proof
  apply EndpointMapMultigraph.incident_swap end₁ end₂ v F

/--
[degreeWithin_swap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/EndpointMapMultigraph.lean)
-/
@[path]
private lemma degreeWithin_swap_eq
  {end₁ end₂ : E → V}
  {F : Finset E}
  {v : V} :
-- imply
  degreeWithin end₂ end₁ F v = degreeWithin end₁ end₂ F v := by
-- proof
  apply EndpointMapMultigraph.degreeWithin_swap end₁ end₂ F v

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
[support_swap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/EndpointMapMultigraph.lean)
-/
@[path]
private lemma support_swap_eq
  {end₁ end₂ : E → V}
  {F : Finset E} :
-- imply
  support end₂ end₁ F = support end₁ end₂ F := by
-- proof
  apply EndpointMapMultigraph.support_swap end₁ end₂ F

/--
[adjacentUsing_symm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/EndpointMapMultigraph.lean)
-/
@[path]
private lemma adjacentUsing_symm_eq
  {end₁ end₂ : E → V}
  {F : Finset E}
  {u v : V} :
-- imply
  AdjacentUsing end₁ end₂ F u v ↔ AdjacentUsing end₁ end₂ F v u := by
-- proof
  apply EndpointMapMultigraph.adjacentUsing_symm end₁ end₂ F

/--
[adjacentUsing_swap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/EndpointMapMultigraph.lean)
-/
@[path]
private lemma adjacentUsing_swap_eq
  {end₁ end₂ : E → V}
  {F : Finset E}
  {u v : V} :
-- imply
  AdjacentUsing end₂ end₁ F u v ↔ AdjacentUsing end₁ end₂ F u v := by
-- proof
  apply EndpointMapMultigraph.adjacentUsing_swap end₁ end₂ F u v

/--
[isConnectedOnSupport_swap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/EndpointMapMultigraph.lean)
-/
@[path]
private lemma isConnectedOnSupport_swap_eq
  {end₁ end₂ : E → V}
  {F : Finset E} :
-- imply
  IsConnectedOnSupport end₂ end₁ F ↔ IsConnectedOnSupport end₁ end₂ F := by
-- proof
  apply EndpointMapMultigraph.isConnectedOnSupport_swap end₁ end₂ F

/--
[isCircuit_swap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/EndpointMapMultigraph.lean)
-/
@[path]
private lemma isCircuit_swap_eq
  {end₁ end₂ : E → V}
  {F : Finset E} :
-- imply
  IsCircuit end₂ end₁ F ↔ IsCircuit end₁ end₂ F := by
-- proof
  apply EndpointMapMultigraph.isCircuit_swap end₁ end₂ F

/--
[degreeWithin_eq_card_incident_of_loopless](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/EndpointMapMultigraph.lean)
-/
@[path]
private lemma degreeWithin_eq_card_incident_of_loopless_eq
  {end₁ end₂ : E → V}
  {F : Finset E}
  {v : V}
-- given
  (h : ∀ e ∈ F, end₁ e ≠ end₂ e) :
-- imply
  degreeWithin end₁ end₂ F v = (incident end₁ end₂ v F).card := by
-- proof
  apply EndpointMapMultigraph.degreeWithin_eq_card_incident_of_loopless end₁ end₂ F v h

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
[cut_swap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/EndpointMapMultigraph.lean)
-/
@[path]
private lemma cut_swap_eq
  [Fintype E]
  {end₁ end₂ : E → V}
  {X : Finset V} :
-- imply
  cut end₂ end₁ X = cut end₁ end₂ X := by
-- proof
  apply EndpointMapMultigraph.cut_swap end₁ end₂ X

/--
[degreeWithin_singleton_loop](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/EndpointMapMultigraph.lean)
-/
@[path]
private lemma degreeWithin_singleton_loop_eq
  {end₁ end₂ : E → V}
  {e : E}
-- given
  (h : end₁ e = end₂ e) :
-- imply
  degreeWithin end₁ end₂ {e} (end₁ e) = 2 := by
-- proof
  apply EndpointMapMultigraph.degreeWithin_singleton_loop end₁ end₂ e h

/--
[loop_not_mem_cut](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/EndpointMapMultigraph.lean)
-/
@[path]
private lemma loop_not_mem_cut_eq
  [Fintype E]
  {end₁ end₂ : E → V}
  {X : Finset V}
  {e : E}
-- given
  (h : end₁ e = end₂ e) :
-- imply
  e ∉ cut end₁ end₂ X := by
-- proof
  apply EndpointMapMultigraph.loop_not_mem_cut end₁ end₂ X e h

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

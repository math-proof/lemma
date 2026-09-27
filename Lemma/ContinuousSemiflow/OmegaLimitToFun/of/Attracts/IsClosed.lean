import Mathlib.Dynamics.OmegaLimit
import Mathlib.Dynamics.Flow
import sympy.dynamics.actor_critic
import sympy.Basic
import Lemma.OmegaLimit.In_OmegaLimit.is.All_In_Closure_Image2_Ici
open Filter Topology


@[main]
private lemma main
  {α : Type*} [TopologicalSpace α] [RegularSpace α]
  {Φ : ContinuousSemiflow α}
  {K : Set α}
  {B : Set α}
-- given
  (h₀ : IsClosed B)
  (h₁ : Φ.Attracts K B) :
-- imply
  omegaLimit atTop Φ.toFun K ⊆ B := by
-- proof
  intro y hy
  by_contra hyB
  obtain ⟨U, ⟨hU, hBU⟩, V, ⟨hyV, hV⟩, hUV⟩ := ((hasBasis_nhdsSet B).disjoint_iff (nhds_basis_opens y)).1 (RegularSpace.regular h₀ hyB)
  obtain ⟨T, -, hTail⟩ := h₁ U hU hBU
  obtain ⟨_, hzV, s, hs, x, hx, rfl⟩ := mem_closure_iff_nhds.1 ((OmegaLimit.In_OmegaLimit.is.All_In_Closure_Image2_Ici Φ.toFun K y).1 hy T) V (hV.mem_nhds hyV)
  exact Set.disjoint_left.1 hUV (hTail s hs x hx) hzV


-- created on 2026-09-26

import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.HeckeAlgebra.HeckeStructureTheorem
open Module BNPairOmegaContext FullBNPairContext


namespace BNPairOmegaContext

/--
[algHomOmega_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/HeckeAlgebra/HeckeStructureTheorem.lean)
-/
@[path]
private lemma algHomOmega_injective
  {k : Type u}
  [CommRing k]
  {Ω : Type u}
  [Group Ω]
  {ctx : BNPairOmegaContext k Ω} :
-- imply
  Function.Injective ctx.algHomOmega := by
-- proof
  intro x y hxy
  suffices h : ∀ (a : MonoidAlgebra k Ω), ctx.algHomOmega a = 0 → a = 0 by
    have := h (x - y) (by rw [map_sub]; exact sub_eq_zero.mpr hxy)
    exact sub_eq_zero.mp this
  intro a ha
  have hli := ctx.ch_linearIndependent
  rw [linearIndependent_iff] at hli
  apply hli
  rw [Finsupp.linearCombination_apply]
  simp only [algHomOmega, MonoidAlgebra.lift_apply, chMonoidHom] at ha
  exact ha

end BNPairOmegaContext

namespace FullBNPairContext

/--
[ch_full_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/HeckeAlgebra/HeckeStructureTheorem.lean)
-/
@[path]
private lemma ch_full_injective
  {k : Type u}
  [CommRing k]
  {Ω : Type u}
  [Group Ω]
  {W : Type u}
  [Group W]
  {ctx : FullBNPairContext k Ω W}
  [Nontrivial k] :
-- imply
  Function.Injective ctx.ch_full := by
-- proof
  intro ⟨σ₁, w₁⟩ ⟨σ₂, w₂⟩ h
  have h₁ := ctx.H_basis_eq (σ₁, w₁)
  have h₂ := ctx.H_basis_eq (σ₂, w₂)
  rw [← h₁, ← h₂] at h
  exact ctx.H_basis.injective h
/-- The Hecke structure theorem for a generalized BN-pair (Section 6.3 of Garrett):
$H$ has a $k$-basis indexed by $Ω × W$, multiplication splits as
$T_{(σ,w)} · T_{(τ,w')} = T_{(στ,1)} · \iota(\mathrm{ch}_o(τ·w) · \mathrm{ch}_o(w'))$,
the joint basis factors as $T_{(σ,w)} = \mathrm{ch}_Ω(σ) · \iota(\mathrm{ch}_o(w))$,
`ch_full` is injective, and $T_{(1,1)} = 1 = \mathrm{ch}_Ω(1)$. -/
end FullBNPairContext


-- created on 2026-10-23
-- updated on 2026-10-24

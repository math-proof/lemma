import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.EllipticCurves.code.CMDefinition
open ComplexMultiplication
open ComplexLattice


namespace ComplexMultiplication

/--
[hasCM_iff_exists_hasCMBy](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMDefinition.lean)
-/
@[path]
lemma hasCM_iff_exists_hasCMBy
  {L : ComplexLattice} :
-- imply
  HasCM L ↔ ∃ 𝒪 : Subring ℂ, HasCMBy L 𝒪 := by
-- proof
  constructor
  · intro ⟨τ, hτ_mem, hτ_not_int⟩
    refine ⟨L.endomorphismRing, ?_, ?_⟩
    · exact rfl
    · exact endomorphismRing_order_witness L τ hτ_mem hτ_not_int
  · intro ⟨𝒪, h𝒪_prop, h𝒪_imag⟩
    obtain ⟨τ, hτ_mem, hτ_not_int, _b, _c, _hpoly, _hdisc⟩ := h𝒪_imag
    have : L.endomorphismRing = 𝒪 := h𝒪_prop
    exact ⟨τ, this ▸ hτ_mem, hτ_not_int⟩

end ComplexMultiplication

namespace ComplexMultiplication

/--
[hasCM_iff_isImagQuadOrder](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMDefinition.lean)
-/
@[path]
lemma hasCM_iff_isImagQuadOrder
  {L : ComplexLattice} :
-- imply
  HasCM L ↔ ComplexLattice.IsImagQuadOrder L.endomorphismRing := by
-- proof
  constructor
  · intro ⟨τ, hτ_mem, hτ_not_int⟩
    obtain ⟨τ', hτ'_mem, hτ'_not_int, b, c, hpoly, hdisc⟩ :=
      endomorphismRing_order_witness L τ hτ_mem hτ_not_int
    exact ⟨τ', hτ'_mem, hτ'_not_int, b, c, hpoly, hdisc⟩
  · intro ⟨τ, hτ_mem, hτ_not_int, _⟩
    exact ⟨τ, hτ_mem, hτ_not_int⟩

end ComplexMultiplication

namespace ComplexMultiplication

/--
[not_hasCM_iff_endRing_eq_Z](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMDefinition.lean)
-/
@[path]
lemma not_hasCM_iff_endRing_eq_Z
  {L : ComplexLattice} :
-- imply
  ¬ HasCM L ↔ ∀ α : ℂ, α ∈ L.endomorphismRing → ∃ n : ℤ, α = (n : ℂ) := by
-- proof
  constructor
  · intro h α hα
    by_contra hne
    push_neg at hne
    exact h ⟨α, hα, hne⟩
  · intro h ⟨τ, hτ_mem, hτ_not_int⟩
    obtain ⟨n, rfl⟩ := h τ hτ_mem
    exact hτ_not_int n rfl
end



-- created on 2026-10-23

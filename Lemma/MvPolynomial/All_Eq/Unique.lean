import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraNotes.code.Polynomials
open Polynomials


namespace Polynomials

/--
[polynomial_mapping_property](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/Polynomials.lean)
-/
@[path]
lemma polynomial_mapping_property
  [CommRing R]
  [CommRing S]
  {φ : R →+* S}
  {α : σ → S} :
-- imply
  (∃! ψ : MvPolynomial σ R →+* S, (∀ r : R, ψ (MvPolynomial.C r) = φ r) ∧ (∀ i : σ, ψ (MvPolynomial.X i) = α i)) := by
-- proof
  refine ⟨eval₂Hom φ α, ⟨eval₂Hom_C φ α, eval₂Hom_X' φ α⟩, ?_⟩
  intro ψ ⟨hC, hX⟩
  exact ringHom_ext (fun r => by rw [hC, eval₂Hom_C]) (fun i => by rw [hX, eval₂Hom_X'])

end Polynomials


-- created on 2026-10-23

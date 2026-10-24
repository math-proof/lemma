import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.SerrePairingNondegenerate
open SerrePairingNondegenerate


namespace SerrePairingNondegenerate

/--
[SerrePairingData.serrePairing_mk](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerrePairingNondegenerate.lean)
-/
@[path]
lemma SerrePairingData.serrePairing_mk
  {k : Type*}
  [Field k]
  {k}
  {D : SerrePairingData k}
  {f : D.K} :
-- imply
  D.serrePairing (Submodule.Quotient.mk f) = D.residuePairing f :=
-- proof
  rfl

end SerrePairingNondegenerate

namespace SerrePairingNondegenerate

/--
[SerrePairingData.pairing_nondegenerate_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerrePairingNondegenerate.lean)
-/
@[path]
lemma SerrePairingData.pairing_nondegenerate_right
  {k : Type*}
  [Field k]
  {k}
  {D : SerrePairingData k}
  {ω : D.H0dual}
-- given
  (h : ∀ (ξ : D.H1), (D.serrePairing ξ) ω = 0) :
-- imply
  ω = 0 := by
-- proof
  apply D.residue_separating ω
  intro f
  have := h (Submodule.Quotient.mk f)
  rwa [D.serrePairing_mk] at this

end SerrePairingNondegenerate

namespace SerrePairingNondegenerate

/--
[PerfectSerrePairingData.pairing_nondegenerate_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerrePairingNondegenerate.lean)
-/
@[path]
lemma PerfectSerrePairingData.pairing_nondegenerate_left
  {k : Type*}
  [Field k]
  {k}
  {D : PerfectSerrePairingData k}
  {ξ : D.toSerrePairingData.H1}
-- given
  (h : ∀ (ω : D.H0dual), (D.toSerrePairingData.serrePairing ξ) ω = 0) :
-- imply
  ξ = 0 := by
-- proof
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
  have hf : f ∈ D.V₁ ⊔ D.V₂ := by
    apply D.residue_separating_left
    intro ω
    have := h ω
    rwa [D.toSerrePairingData.serrePairing_mk] at this
  exact (Submodule.Quotient.mk_eq_zero _).mpr hf

end SerrePairingNondegenerate

namespace SerrePairingNondegenerate

/--
[PerfectSerrePairingData.pairing_perfect](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerrePairingNondegenerate.lean)
-/
@[path]
lemma PerfectSerrePairingData.pairing_perfect
  {k : Type*}
  [Field k]
  {k}
  {D : PerfectSerrePairingData k} :
-- imply
  (∀ (ω : D.H0dual), (∀ (ξ : D.toSerrePairingData.H1), (D.toSerrePairingData.serrePairing ξ) ω = 0) → ω = 0) ∧ (∀ (ξ : D.toSerrePairingData.H1), (∀ (ω : D.H0dual), (D.toSerrePairingData.serrePairing ξ) ω = 0) → ξ = 0) :=
-- proof
  ⟨D.toSerrePairingData.pairing_nondegenerate_right,
    D.pairing_nondegenerate_left⟩

end SerrePairingNondegenerate


-- created on 2026-10-23

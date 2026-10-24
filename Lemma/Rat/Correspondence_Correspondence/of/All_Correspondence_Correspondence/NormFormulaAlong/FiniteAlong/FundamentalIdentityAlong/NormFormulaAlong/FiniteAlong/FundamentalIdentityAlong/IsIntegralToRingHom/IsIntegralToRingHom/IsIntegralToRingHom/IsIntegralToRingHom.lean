import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_AlgebraicCurve_Correspondence
import Lemma.Int.P2MUtil

open IsDedekindDomain AlgebraicCurve

/--
[AlgebraicCurve_Pic0_correspondence_correspondence_comm](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_Pic0_correspondence_correspondence_comm.lean)
-/
@[path]
private lemma main
  {K F F₁ F₂ : Type*} [Field K] [Field F] [Field F₁] [Field F₂] [Algebra K F] [Algebra K F₁] [Algebra K F₂] [HasPrincipalDivisors K F₁] [HasPrincipalDivisors K F₂]
  {φ ψ : F →ₐ[K] F₁}
  {φ' ψ' : F →ₐ[K] F₂}
  {x : Pic0 K F}
-- given
  (hφ : φ.toRingHom.IsIntegral)
  (hψ : ψ.toRingHom.IsIntegral)
  (hφ' : φ'.toRingHom.IsIntegral)
  (hψ' : ψ'.toRingHom.IsIntegral)
  (hFI : FundamentalIdentityAlong K φ hφ)
  (hfin : FiniteAlong K ψ)
  (hN : NormFormulaAlong K ψ hfin)
  (hFI' : FundamentalIdentityAlong K φ' hφ')
  (hfin' : FiniteAlong K ψ')
  (hN' : NormFormulaAlong K ψ' hfin')
  (hcomm : ∀ D : Divisor K F, Divisor.correspondence φ ψ hφ hψ (Divisor.correspondence φ' ψ' hφ' hψ' D) = Divisor.correspondence φ' ψ' hφ' hψ' (Divisor.correspondence φ ψ hφ hψ D)) :
-- imply
  Pic0.correspondence φ ψ hφ hψ hFI hfin hN (Pic0.correspondence φ' ψ' hφ' hψ' hFI' hfin' hN' x) = Pic0.correspondence φ' ψ' hφ' hψ' hFI' hfin' hN' (Pic0.correspondence φ ψ hφ hψ hFI hfin hN x) := by
-- proof
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [Pic0.correspondence_mk, Pic0.correspondence_mk, Pic0.correspondence_mk, Pic0.correspondence_mk]
  exact congrArg Pic0.mk (Subtype.ext (hcomm (D : Divisor K F)))


-- created on 2026-10-23

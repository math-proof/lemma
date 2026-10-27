import Mathlib
import Initialize.Tactic.Attr.Basic
open Polynomial


namespace Algebra.FormallyUnramified

/--
[of_isUnit_aeval_derivative_of_adjoin_eq_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/LocalRing/Etale.lean)
-/
@[path]
lemma of_isUnit_aeval_derivative_of_adjoin_eq_top
  [CommRing R] [CommRing S] [Algebra R S]
  {x : S}
  {P : R[X]}
-- given
  (hP : aeval x P = 0)
  (hP' : IsUnit (aeval x P.derivative))
  (hx : Algebra.adjoin R {x} = ⊤) :
-- imply
  Algebra.FormallyUnramified R S := by
-- proof
  let D := KaehlerDifferential.D R S
  have hDx : D x = 0 := by
    apply hP'.smul_eq_zero.mp
    rw [← D.map_aeval P x, hP, D.map_zero]
  have hD : D = 0 := by
    apply Derivation.ext_of_adjoin_eq_top ({x} : Set S) hx
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    simpa using hDx
  refine ⟨(subsingleton_iff_forall_eq 0).mpr ?_⟩
  intro y
  have hle : (⊤ : Submodule S Ω[S⁄R]) ≤ ⊥ := by
    rw [← KaehlerDifferential.span_range_derivation]
    apply Submodule.span_le.mpr
    rintro _ ⟨s, rfl⟩
    change D s ∈ (⊥ : Submodule S Ω[S⁄R])
    rw [hD]
    simp
  have hy : y = 0 := (Submodule.mem_bot S).mp (hle Submodule.mem_top)
  exact hy
end Algebra.FormallyUnramified


namespace Algebra

/--
[etale_iff_exists_adjoin_eq_top_and_separable_map_minpoly](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/LocalRing/Etale.lean)
-/
@[path]
lemma etale_iff_exists_adjoin_eq_top_and_separable_map_minpoly
  [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R] [IsLocalRing S] [Module.Finite R S] [FaithfulSMul R S] [Module.Flat R S] [Algebra.FinitePresentation R S] :
-- imply
  Algebra.Etale R S ↔
      ∃ x : S, Algebra.adjoin R ({x} : Set S) = ⊤ ∧
        ((minpoly R x).map (IsLocalRing.residue R)).Separable := by
-- proof
  constructor
  · intro hE
    let _ : Algebra.Etale R S := hE
    obtain ⟨x, hx⟩ := IsLocalRing.exists_adjoin_eq_top (R := R) (S := S)
    refine ⟨x, hx, ?_⟩
    rw [IsLocalRing.minpoly_map_residue hx]
    exact Algebra.IsSeparable.isSeparable _ (IsLocalRing.residue S x)
  · rintro ⟨x, hx, hsep⟩
    have hroot : aeval (IsLocalRing.residue S x)
      ((minpoly R x).map (IsLocalRing.residue R)) = 0 := by
      rw [← map_aeval_eq_aeval_map (ψ := IsLocalRing.residue S)
        (φ := IsLocalRing.residue R) rfl]
      simp [minpoly.aeval R x]
    have hunit : IsUnit (aeval x (minpoly R x).derivative) := by
      apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
      rw [map_aeval_eq_aeval_map (ψ := IsLocalRing.residue S)
        (φ := IsLocalRing.residue R) rfl, ← derivative_map]
      exact hsep.aeval_derivative_ne_zero hroot
    let _ : Algebra.FormallyUnramified R S :=
      FormallyUnramified.of_isUnit_aeval_derivative_of_adjoin_eq_top x
        (minpoly R x) (minpoly.aeval R x) hunit hx
    exact Algebra.Etale.of_formallyUnramified_of_flat

end Algebra


-- created on 2026-10-20
-- updated on 2026-10-26

import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_IharaLemma_IdempotentSplitting
open IharaLemma


/-- ported from external source -/
@[path]
private lemma main
  [CommRing 𝒪] [IsLocalRing 𝒪] [CommRing B] [Algebra 𝒪 B]
  {Sp : IdempotentSplitting B}
  {i : Fin Sp.n}
  {π : Sp.CornerRing i →ₐ[𝒪] IsLocalRing.ResidueField 𝒪}
  {x : B} :
-- imply
  x ∈ Sp.𝔪 i ↔ π (Sp.toCornerRing i x) = 0 := by
  classical
    have hπsurj : Function.Surjective π := by
-- proof
      intro y
      obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective y
      exact ⟨algebraMap 𝒪 _ r, π.commutes r⟩
    set f : B →+* IsLocalRing.ResidueField 𝒪 := π.toRingHom.comp (Sp.toCornerRing i) with hf
    have hfsurj : Function.Surjective f := by
      intro y
      obtain ⟨z, rfl⟩ := hπsurj y
      obtain ⟨_, b, rfl⟩ := z
      refine ⟨b, ?_⟩
      show π (Sp.toCornerRing i b) = π ⟨Sp.e i * b * Sp.e i, b, rfl⟩
      rfl
    have hmax : (RingHom.ker f).IsMaximal := RingHom.ker_isMaximal_of_surjective f hfsurj
    have hle : RingHom.ker f ≤ Sp.𝔪 i := by
      intro s hs
      by_contra hs'
      have hu : IsUnit (Sp.toCornerRing i s) :=
        IsLocalization.map_units (M := (Sp.𝔪 i).primeCompl) (Sp.CornerRing i) ⟨s, hs'⟩
      have h0 : π (Sp.toCornerRing i s) = 0 := hs
      refine (hu.map π).ne_zero h0
    have heq : RingHom.ker f = Sp.𝔪 i := by
      exact hmax.eq_of_le (Sp.isMaximal i).ne_top hle
    rw [← heq, RingHom.mem_ker]
    rfl


-- created on 2026-10-23

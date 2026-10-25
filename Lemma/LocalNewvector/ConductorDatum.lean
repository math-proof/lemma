import Lemma.LocalNewvector.CongruenceSubgroupK1
import Lemma.RepTheory.GL2CongruenceSubgroup
import Lemma.LocalLanglands.LocalHeckeInstance
import Def.LocalNewvector_ConductorDatum

set_option autoImplicit false

noncomputable section

namespace LocalNewvector


theorem mem_fixedSubmodule_iff {G : Type*} [Group G] {U : Subgroup G} {V : Type*}
    [AddCommGroup V] [Module ℂ V] [DistribMulAction G V] [SMulCommClass G ℂ V] {v : V} :
    v ∈ fixedSubmodule U V ↔ ∀ g ∈ U, g • v = v :=
  Iff.rfl

section IntegralSubgroupSeam

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

theorem congruenceK0_zero_eq_integralSubgroup (ϖ : R) :
    congruenceK0 (K := K) ϖ 0 = LocalGL2.integralSubgroup R K :=
  congruenceK0_zero ϖ

theorem congruenceK1_zero_eq_integralSubgroup (ϖ : R) :
    congruenceK1 (K := K) ϖ 0 = LocalGL2.integralSubgroup R K :=
  congruenceK1_zero ϖ

theorem congruenceK0_le_integralSubgroup (ϖ : R) (n : ℕ) :
    congruenceK0 (K := K) ϖ n ≤ LocalGL2.integralSubgroup R K := by
  rintro x ⟨y, rfl, _⟩
  exact ⟨y, rfl⟩

theorem congruenceK1_le_integralSubgroup (ϖ : R) (n : ℕ) :
    congruenceK1 (K := K) ϖ n ≤ LocalGL2.integralSubgroup R K :=
  (congruenceK1_le_congruenceK0 _ _).trans (congruenceK0_le_integralSubgroup ϖ n)

end IntegralSubgroupSeam

section Padic

variable (p : ℕ) [Fact p.Prime]

theorem padicK0_zero_eq_integralSubgroup :
    padicK0 p 0 = LocalGL2.integralSubgroup ℤ_[p] ℚ_[p] :=
  congruenceK0_zero_eq_integralSubgroup (p : ℤ_[p])

theorem padicK1_zero_eq_integralSubgroup :
    padicK1 p 0 = LocalGL2.integralSubgroup ℤ_[p] ℚ_[p] :=
  congruenceK1_zero_eq_integralSubgroup (p : ℤ_[p])


theorem centralCharacterRep_unique {V : Type*} [AddCommGroup V] [Module ℂ V]
    [DistribMulAction (GL (Fin 2) ℚ_[p]) V] (hV : ∃ v : V, v ≠ 0)
    {ω ω' : ℚ_[p]ˣ →* ℂˣ} (hω : IsCentralCharacterRep p V ω)
    (hω' : IsCentralCharacterRep p V ω') : ω = ω' := by
  obtain ⟨v, hv0⟩ := hV
  have key : ∀ u : ℚ_[p]ˣ, (ω u : ℂ) = (ω' u : ℂ) := by
    intro u
    by_contra hne
    have hcne : (ω u : ℂ) - (ω' u : ℂ) ≠ 0 := sub_ne_zero.mpr hne
    have h3 : ((ω u : ℂ) - (ω' u : ℂ)) • v = 0 := by
      rw [sub_smul, ← hω u v, ← hω' u v, sub_self]
    exact hv0 (by
      calc v = ((ω u : ℂ) - (ω' u : ℂ))⁻¹ • (((ω u : ℂ) - (ω' u : ℂ)) • v) := by
            rw [smul_smul, inv_mul_cancel₀ hcne, one_smul]
        _ = 0 := by rw [h3, smul_zero])
  exact MonoidHom.ext fun u => Units.ext (key u)


theorem hasNewvectorConductor_unique {V : Type*} [AddCommGroup V] [Module ℂ V]
    [DistribMulAction (GL (Fin 2) ℚ_[p]) V] [SMulCommClass (GL (Fin 2) ℚ_[p]) ℂ V]
    {c c' : ℕ} (h : HasNewvectorConductor p V c) (h' : HasNewvectorConductor p V c') :
    c = c' := by
  rcases lt_trichotomy c c' with hlt | heq | hgt
  · exact absurd (h'.2 c hlt) h.1
  · exact heq
  · exact absurd (h.2 c' hgt) h'.1

end Padic

end LocalNewvector

end

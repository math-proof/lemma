import Mathlib
import Lemma.Definitions.Def_Deformations_ContinuousSMulDiscrete

section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

namespace IsArithFrobAt

open scoped Pointwise

variable {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
variable {Q : Ideal S} {σ σ' : G}

variable [TopologicalSpace G] [CompactSpace G] [TotallyDisconnectedSpace G]
variable [IsTopologicalGroup G] [Algebra.IsInvariant R S G]
variable [ContinuousSMulDiscrete G S]

variable (R G Q) in
attribute [local instance] Ideal.Quotient.field in

lemma exists_of_isInvariant_of_profinite
    [Q.IsMaximal] [Finite (R ⧸ Q.under R)] : ∃ σ : G, IsArithFrobAt R σ Q := by
  letI : TopologicalSpace S := ⊥
  letI : DiscreteTopology S := ⟨rfl⟩
  let P := Q.under R
  have : Algebra.IsIntegral R S := Algebra.IsInvariant.isIntegral_of_profinite (G := G)
  have : P.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q
  obtain ⟨p, hc⟩ := CharP.exists (R ⧸ P)
  cases nonempty_fintype (R ⧸ P)
  obtain ⟨k, hp, hk⟩ := FiniteField.card (R ⧸ P) p
  have := CharP.of_ringHom_of_ne_zero (algebraMap (R ⧸ P) (S ⧸ Q)) p hp.ne_zero
  have : ExpChar (S ⧸ Q) p := .prime hp
  have : PerfectField (S ⧸ Q) := Algebra.IsAlgebraic.perfectField (K := (R ⧸ P))
  let l : (S ⧸ Q) ≃ₐ[R ⧸ P] S ⧸ Q :=
    { __ := iterateFrobeniusEquiv (S ⧸ Q) p k,
      commutes' r := by
        dsimp [iterateFrobenius_def]
        rw [← map_pow, ← hk, FiniteField.pow_card] }
  obtain ⟨σ, hσ⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := G) P Q l
  refine ⟨σ, fun x ↦ ?_⟩
  rw [← Ideal.Quotient.eq, Nat.card_eq_fintype_card, hk]
  exact DFunLike.congr_fun hσ (Ideal.Quotient.mk Q x)

variable (S G) in
lemma exists_primesOver_isConj_of_profinite (P : Ideal R) [Finite (R ⧸ P)] [P.IsPrime] :
    ∃ σ : Ideal.primesOver P S → G, (∀ Q, IsArithFrobAt R (σ Q) Q.1) ∧
      (∀ Q₁ Q₂, IsConj (σ Q₁) (σ Q₂)) := by
  letI : TopologicalSpace S := ⊥
  letI : DiscreteTopology S := ⟨rfl⟩
  have hP : P.IsMaximal := Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain (R ⧸ P))
  have : Algebra.IsIntegral R S := Algebra.IsInvariant.isIntegral_of_profinite (G := G)
  obtain hs | ⟨Q, hQ, hQ₂⟩ := Set.eq_empty_or_nonempty (Ideal.primesOver P S)
  · simp [hs]
  have (Q' : Ideal.primesOver P S) : ∃ σ : G, Q'.1 = σ • Q :=
    Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite _ _ (hQ₂.over.symm.trans Q'.2.2.over)
  choose τ hτ using this
  have : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := R) Q
    (by rwa [← Ideal.under, ← hQ₂.over])
  have : Finite (R ⧸ Q.under R) := by rwa [← hQ₂.over]
  obtain ⟨σ, hσ⟩ := exists_of_isInvariant_of_profinite R G Q
  refine ⟨fun Q' ↦ τ Q' * σ * (τ Q')⁻¹, fun Q' ↦ hτ Q' ▸ hσ.conj (τ Q'), fun Q₁ Q₂ ↦
    .trans (.symm (isConj_iff.mpr ⟨τ Q₁, rfl⟩)) (isConj_iff.mpr ⟨τ Q₂, rfl⟩)⟩

variable (R G Q)

noncomputable
def _root_.arithFrobAt' [Q.IsPrime] [Finite (R ⧸ Q.under R)] : G :=
  (exists_primesOver_isConj_of_profinite S G (Q.under R)).choose ⟨Q, ‹_›, ⟨rfl⟩⟩

protected lemma arithFrobAt' [Q.IsPrime] [Finite (R ⧸ Q.under R)] :
    IsArithFrobAt R (arithFrobAt' R G Q) Q :=
  (exists_primesOver_isConj_of_profinite S G (Q.under R)).choose_spec.1 ⟨Q, ‹_›, ⟨rfl⟩⟩

lemma _root_.isConj_arithFrobAt'
    [Q.IsPrime] [Finite (R ⧸ Q.under R)] (Q' : Ideal S) [Q'.IsPrime] [Finite (R ⧸ Q'.under R)]
    (H : Q.under R = Q'.under R) : IsConj (arithFrobAt' R G Q) (arithFrobAt' R G Q') := by
  obtain ⟨P, hP, h₁, h₂, h₃⟩ :
      ∃ P : Ideal R, P.IsPrime ∧ P = Q.under R ∧ P = Q'.under R ∧ Finite (R ⧸ P) :=
    ⟨Q.under R, inferInstance, rfl, H, ‹_›⟩
  convert (exists_primesOver_isConj_of_profinite S G P).choose_spec.2
    ⟨Q, ‹_›, ⟨h₁⟩⟩ ⟨Q', ‹_›, ⟨h₂⟩⟩
  · subst h₁; rfl
  · subst h₂; rfl

end IsArithFrobAt

end

import sympy.Basic
import Mathlib

open IsLocalRing

/-! FLT AdicCompletion existence axioms shared by path lemmas (not rendered). -/

axiom AdicCompletion.exists_algebra_moduleFinite_of_moduleFinite_of_isMaximal
  (B C : Type*) [CommRing B] [IsNoetherianRing B] [CommRing C] [Algebra B C] [Module.Finite B C]
  (𝔫 : Ideal C) [𝔫.IsMaximal] : Nonempty
    (Σ' (_ : Algebra (AdicCompletion (Ideal.comap (algebraMap B C) 𝔫) B) (AdicCompletion 𝔫 C))
      (_ : IsScalarTower B (AdicCompletion (Ideal.comap (algebraMap B C) 𝔫) B) (AdicCompletion 𝔫 C)),
      Module.Finite (AdicCompletion (Ideal.comap (algebraMap B C) 𝔫) B) (AdicCompletion 𝔫 C) ∧
        (Module.Flat B C →
          Function.Injective (algebraMap (AdicCompletion (Ideal.comap (algebraMap B C) 𝔫) B)
            (AdicCompletion 𝔫 C))))

axiom AdicCompletion.exists_ringEquiv_quotient_map_adicCompletion_quotient
  (N : Type*) [CommRing N] [IsNoetherianRing N] (I 𝔭 : Ideal N) : Nonempty
    (Σ' (e : RingEquiv (AdicCompletion I N ⧸ 𝔭.map (algebraMap N (AdicCompletion I N)))
        (AdicCompletion (I.map (Ideal.Quotient.mk 𝔭)) (N ⧸ 𝔭))),
      ∀ x : N, e (Ideal.Quotient.mk _ (algebraMap N (AdicCompletion I N) x)) =
        algebraMap (N ⧸ 𝔭) (AdicCompletion (I.map (Ideal.Quotient.mk 𝔭)) (N ⧸ 𝔭))
          (Ideal.Quotient.mk 𝔭 x))

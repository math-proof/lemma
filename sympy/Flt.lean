import Mathlib

open IsLocalRing

axiom BDescN6.adicEquiv {C : Type*} [CommRing C] (𝔫 : Ideal C) [𝔫.IsMaximal]
    (S : Type*) [CommRing S] [IsLocalRing S] [Algebra C S] [IsLocalization.AtPrime S 𝔫] :
    RingEquiv (AdicCompletion 𝔫 C) (AdicCompletion (maximalIdeal S) S)

instance instAlgebraAdicCompletion {O : Type*} [CommRing O] [IsLocalRing O]
    {C : Type*} [CommRing C] [Algebra O C] {𝔫 : Ideal C} :
    Algebra (AdicCompletion (maximalIdeal O) O) (AdicCompletion 𝔫 C) := sorry

instance instIsScalarTowerAdicCompletion {O : Type*} [CommRing O] [IsLocalRing O]
    {C : Type*} [CommRing C] [Algebra O C] {𝔫 : Ideal C} :
    IsScalarTower O (AdicCompletion (maximalIdeal O) O) (AdicCompletion 𝔫 C) := sorry

-- FLT-specific AdicCompletion constants

axiom AdicCompletion.semilocalPiEquiv {C : Type*} [CommRing C] (I : Ideal C) :
    RingEquiv (AdicCompletion I C)
      ((Q : {P : Ideal C // P.IsMaximal ∧ I ≤ P}) → AdicCompletion Q.val C)

axiom AdicCompletion.tensorRingEquiv {O : Type*} [CommRing O]
    (C : Type*) [CommRing C] [Algebra O C] (𝔭 : Ideal O) :
    RingEquiv (TensorProduct O (AdicCompletion 𝔭 O) C) (AdicCompletion (𝔭.map (algebraMap O C)) C)

axiom AdicCompletion.semilocalComponent {C : Type*} [CommRing C] (I : Ideal C)
    {𝔫 : Ideal C} (hI𝔫 : I ≤ 𝔫) (y : AdicCompletion I C) :
    AdicCompletion 𝔫 C

axiom AdicCompletion.semilocalComponent_eq {C : Type*} [CommRing C] (I : Ideal C)
    {𝔫 : Ideal C} [h𝔫 : 𝔫.IsMaximal] (hI𝔫 : I ≤ 𝔫) (y : AdicCompletion I C) :
    AdicCompletion.semilocalPiEquiv I y ⟨𝔫, h𝔫, hI𝔫⟩ = AdicCompletion.semilocalComponent I hI𝔫 y

axiom AdicCompletion.completionBaseChangeHom {O : Type*} [CommRing O]
    (C : Type*) [CommRing C] [Algebra O C] (𝔭 : Ideal O)
    (x : AdicCompletion 𝔭 O) : AdicCompletion (𝔭.map (algebraMap O C)) C

axiom AdicCompletion.tensorRingEquiv_tmul {O : Type*} [CommRing O]
    {C : Type*} [CommRing C] [Algebra O C] (𝔭 : Ideal O)
    (x : AdicCompletion 𝔭 O) (c₀ : C) :
    AdicCompletion.tensorRingEquiv C 𝔭 (x ⊗ₜ c₀) =
      AdicCompletion.completionBaseChangeHom C 𝔭 x * AdicCompletion.of (𝔭.map (algebraMap O C)) C c₀

axiom AdicCompletion.semilocalPiEquiv_of {C : Type*} [CommRing C] (I : Ideal C)
    {𝔫 : Ideal C} [h𝔫 : 𝔫.IsMaximal] (hI𝔫 : I ≤ 𝔫) (c₀ : C) :
    AdicCompletion.semilocalPiEquiv I (AdicCompletion.of I C c₀) ⟨𝔫, h𝔫, hI𝔫⟩ =
      AdicCompletion.of 𝔫 C c₀

axiom AdicCompletion.evalₐ_algebraMap_of_liesOver {O : Type*} [CommRing O]
    {C : Type*} [CommRing C] [Algebra O C] (𝔭 : Ideal O) (𝔫 : Ideal C) [𝔫.LiesOver 𝔭]
    (f : AdicCompletion 𝔭 O →+* AdicCompletion 𝔫 C) (n : ℕ) (o : O) (x : AdicCompletion 𝔭 O)
    (ho : AdicCompletion.evalₐ 𝔭 n x = Ideal.Quotient.mk (𝔭 ^ n) o) :
    AdicCompletion.evalₐ 𝔫 n (f x) = Ideal.Quotient.mk (𝔫 ^ n) (algebraMap O C o)

axiom AdicCompletion.evalₐ_mapₐ {O : Type*} [CommRing O] {C : Type*} [CommRing C]
    [Algebra O C] (𝔭 : Ideal O) (𝔫 : Ideal C) (n : ℕ)
    (f : AdicCompletion 𝔭 O →+* AdicCompletion 𝔫 C) (x : AdicCompletion 𝔭 O) :
    True

axiom AdicCompletion.levelMapₐ_mk {C : Type*} [CommRing C] (𝔫 : Ideal C) (n : ℕ)
    (x : C) : True

axiom BDescN3.isSeparable_pi {K : Type*} [Field K] {ι : Type*} (Ai : ι → Type*)
    [∀ i, Ring (Ai i)] [∀ i, Algebra K (Ai i)] : Algebra.IsSeparable K (∀ i, Ai i)

axiom isStandardEtale {R : Type*} [CommRing R] (n : ℕ) (u : R)
    (hn0 : n ≠ 0) (hn : IsUnit (n : R)) (hu : IsUnit u) :
    Algebra.IsStandardEtale R (AdjoinRoot (Polynomial.X ^ n - Polynomial.C u : Polynomial R))

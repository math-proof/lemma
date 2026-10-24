import Lemma.Definitions.Def_CuspForm_ModPForms

set_option autoImplicit false

namespace ModPForms

structure SSDatum (p : ℕ) (N' : ℕ) (S₀ : Set ℕ) (F : Type) [Field F] [CharP F p] where

  S : ℤ → Type
  addCommGroup : ∀ k, AddCommGroup (S k)
  module : ∀ k, Module F (S k)

  T : ∀ (k : ℤ) (_ : ℕ), letI := addCommGroup k; letI := module k; S k →ₗ[F] S k

  hecke_stable : ∀ (k : ℤ), (p : ℤ) + 2 ≤ k → ∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ N' → ℓ ∉ S₀ →
    ∀ φ ∈ modPMod N' k F, heckePS k ℓ φ ∈ modPMod N' k F

  res : ∀ k : ℤ, (p : ℤ) + 2 ≤ k → letI := addCommGroup k; letI := module k;
    ↥(modPMod N' k F) →ₗ[F] S k

  res_equivariant : ∀ (k : ℤ) (hk : (p : ℤ) + 2 ≤ k) (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N') (hℓS : ℓ ∉ S₀)
    (φ : PowerSeries F) (hφ : φ ∈ modPMod N' k F),
    letI := addCommGroup k; letI := module k;
    res k hk ⟨heckePS k ℓ φ, hecke_stable k hk ℓ hℓ hℓN hℓS φ hφ⟩ = T k ℓ (res k hk ⟨φ, hφ⟩)

  res_ker : ∀ (k : ℤ) (hk : (p : ℤ) + 2 ≤ k) (φ : PowerSeries F) (hφ : φ ∈ modPMod N' k F),
    letI := addCommGroup k; letI := module k;
    res k hk ⟨φ, hφ⟩ = 0 → φ ∈ modPMod N' (k - ((p : ℤ) - 1)) F

  bIso : ∀ k : ℤ, 1 ≤ k → letI := addCommGroup k; letI := module k;
    letI := addCommGroup (k + ((p : ℤ) + 1)); letI := module (k + ((p : ℤ) + 1));
    S k ≃ₗ[F] S (k + ((p : ℤ) + 1))
  bIso_equivariant : ∀ (k : ℤ) (hk : 1 ≤ k) (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ N' → ℓ ∉ S₀ →
    ∀ v : S k,
    letI := addCommGroup k; letI := module k;
    letI := addCommGroup (k + ((p : ℤ) + 1)); letI := module (k + ((p : ℤ) + 1));
    T (k + ((p : ℤ) + 1)) ℓ (bIso k hk v) = (ℓ : F) • bIso k hk (T k ℓ v)

  pullback : ∀ (k' : ℤ), 1 ≤ k' → k' ≤ (p : ℤ) + 1 →
    ∀ (v : S k') (mu : ℕ → F),
    letI := addCommGroup k'; letI := module k';
    v ≠ 0 → (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N' → ℓ ∉ S₀ → T k' ℓ v = mu ℓ • v) →
    ∃ k'' : ℤ, 2 ≤ k'' ∧ k'' ≤ (p : ℤ) + 1 ∧ ∃ (j : ℕ) (ψ : PowerSeries F) (nu : ℕ → F),
      ψ ∈ modPMod N' k'' F ∧ IsModPEigen N' S₀ k'' ψ nu ∧
        ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N' → ℓ ∉ S₀ → nu ℓ = (ℓ : F) ^ j * mu ℓ

end ModPForms

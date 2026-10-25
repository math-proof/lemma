import Structure.CerednikDrinfeld_FormalUpperHalfPlanePoints
import Instance.CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Def.CerednikDrinfeld_SchemeNilpPoints

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree

namespace CerednikDrinfeld
namespace FormalOmega

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure FormalQuotientDatum
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀]
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ) (r : ℕ)
    {G : Type} [Group G] (σ : G →* Matrix.GeneralLinearGroup (Fin 2) K₀) (Γ Γ' : Subgroup G)
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Type 1 where

  Y : ℕ → Scheme.{0}

  yb : ∀ n : ℕ, Y n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))

  yt : ∀ n : ℕ, Y n ⟶ Y (n + 1)

  yt_isPullback : ∀ n : ℕ, IsPullback (yt n) (yb n) (yb (n + 1))
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1)))))))

  yb_isProper : ∀ n : ℕ, IsProper (yb n)

  q : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B], (algebraMap 𝒪 B π) ^ (n + 1) = 0 →
    (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Spec (CommRingCat.of B) ⟶ Y n)

  q_over : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
    (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
    q n B hB x ≫ yb n ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) =
      Spec.map (CommRingCat.ofHom (algebraMap 𝒪 B))

  q_natural : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B']
    (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (hB' : (algebraMap 𝒪 B' π) ^ (n + 1) = 0) (φ : B →ₐ[𝒪] B')
    (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
    q n B' hB' ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x) = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ q n B hB x

  q_yt : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
    (hB' : (algebraMap 𝒪 B π) ^ (n + 1 + 1) = 0) (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
    q (n + 1) B hB' x = q n B hB x ≫ yt n

  q_inv : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (γ : G), γ ∈ Γ →
    ∀ x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B,
      OmegaNr.IsTwistedAct π Onr Fr vdet B (σ γ) x x' → q n B hB x' = q n B hB x

  q_fib : ∀ (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [Algebra 𝒪 k] (hk : (algebraMap 𝒪 k π) ^ (n + 1) = 0)
    (ψ : Onr →ₐ[𝒪] k),
    (∀ η : Spec (CommRingCat.of k) ⟶ Y n,
      η ≫ yb n ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) =
        Spec.map (CommRingCat.ofHom (algebraMap 𝒪 k)) →
      ∃ P : (Omega K₀ π).obj k, q n k hk (ψ, P) = η) ∧
    ∀ P P' : (Omega K₀ π).obj k, q n k hk (ψ, P) = q n k hk (ψ, P') ↔
      ∃ γ ∈ Γ, OmegaNr.IsTwistedAct π Onr Fr vdet k (σ γ) (ψ, P) (ψ, P')

  univ : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪))
    (ρ' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
      (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Scheme.nilpPoints t).obj B),
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
      (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
      ρ' B' hB' ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x) = (Scheme.nilpPoints t).map φ (ρ' B hB x)) →
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : G), γ ∈ Γ →
      ∀ x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B,
        OmegaNr.IsTwistedAct π Onr Fr vdet B (σ γ) x x' → ρ' B hB x' = ρ' B hB x) →
    ∃ u : ∀ n : ℕ, Y n ⟶ T,
      (∀ n : ℕ, u n ≫ t = yb n ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))) ∧
      (∀ n : ℕ, yt n ≫ u (n + 1) = u n) ∧
      (∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
        (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B), q n B hB x ≫ u n = (ρ' B ⟨n + 1, hB⟩ x).1) ∧
      ∀ u' : ∀ n : ℕ, Y n ⟶ T,
        (∀ n : ℕ, u' n ≫ t = yb n ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))) →
        (∀ n : ℕ, yt n ≫ u' (n + 1) = u' n) →
        (∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
          (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B), q n B hB x ≫ u' n = (ρ' B ⟨n + 1, hB⟩ x).1) →
        u' = u

  Ynr : ℕ → Scheme.{0}

  p₁ : ∀ n : ℕ, Ynr n ⟶ Y n

  p₂ : ∀ n : ℕ, Ynr n ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}))

  isPullback_nr : ∀ n : ℕ, IsPullback (p₁ n) (p₂ n)
    (yb n ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))))
    (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}))))

  jnr : ∀ n : ℕ, Ynr n ⟶ Ynr (n + 1)

  jnr_p₁ : ∀ n : ℕ, jnr n ≫ p₁ (n + 1) = p₁ n ≫ yt n

  jnr_p₂ : ∀ n : ℕ, jnr n ≫ p₂ (n + 1) = p₂ n ≫ Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 Onr π) (Nat.le_succ (n + 1))))))

  U : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ), (Ynr n).Opens

  c : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ),
    ↑((Ynr n).presheaf.obj (Opposite.op (U h n))) →+* ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)})

  κ : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ), Spec (CommRingCat.of ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)})) ⟶ Ynr n

  κ_preimage : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ), (κ h n) ⁻¹ᵁ (U h n) = ⊤ ∧
        ∀ (hle : (⊤ : (Spec (CommRingCat.of ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}))).Opens) ≤ (κ h n) ⁻¹ᵁ (U h n))
          (s : ↑((Ynr n).presheaf.obj (Opposite.op (U h n)))),
          c h n s = (Scheme.ΓSpecIso (CommRingCat.of ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}))).hom.hom
            ((Spec (CommRingCat.of ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}))).presheaf.map (homOfLE hle).op (((κ h n).app (U h n)).hom s))

  c_const : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ) (y : Onr),
        c h n ((Ynr n).presheaf.map (homOfLE le_top).op
          ((p₂ n).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}))).inv.hom
            (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}) y)))) =
          Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) y)

  U_jnr : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ),
        U h n = (jnr n) ⁻¹ᵁ (U h (n + 1)) ∧
        ∀ (hle : U h n ≤ (jnr n) ⁻¹ᵁ (U h (n + 1))) (s : ↑((Ynr (n + 1)).presheaf.obj (Opposite.op (U h (n + 1))))),
          c h n ((Ynr n).presheaf.map (homOfLE hle).op (((jnr n).app (U h (n + 1))).hom s)) =
          Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr
            (pow_dvd_pow (algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) (Nat.le_succ (n + 1)))) (c h (n + 1) s)

  κ_p₁ : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ)
          (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra Onr B] [IsScalarTower 𝒪 Onr B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
          (xbar : ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) →ₐ[Onr] B) (d P : DeligneDatum (K := K₀) π B),
          (d.line (stdFullLattice K₀) =
              Submodule.span B {(xbar (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
            d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
              (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (xbar (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (chartERing.η Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
                (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
            d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
          DeligneDatum.IsPullback (K := K₀) (π := π) B h⁻¹ d P →
          Spec.map (CommRingCat.ofHom xbar.toRingHom) ≫ κ h n ≫ p₁ n = q n B hB ((IsScalarTower.toAlgHom 𝒪 Onr B), P)

  cover : ∀ n : ℕ, ⨆ h : Matrix.GeneralLinearGroup (Fin 2) K₀, U h n = ⊤

  functions : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀),
        (∀ (s s' : ∀ m : ℕ, ↑((Ynr m).presheaf.obj (Opposite.op (U h m)))),
          (∀ (m : ℕ) (hle : U h m ≤ (jnr m) ⁻¹ᵁ (U h (m + 1))),
              (Ynr m).presheaf.map (homOfLE hle).op (((jnr m).app (U h (m + 1))).hom (s (m + 1))) = s m) →
          (∀ (m : ℕ) (hle : U h m ≤ (jnr m) ⁻¹ᵁ (U h (m + 1))),
              (Ynr m).presheaf.map (homOfLE hle).op (((jnr m).app (U h (m + 1))).hom (s' (m + 1))) = s' m) →
          (∀ m : ℕ, c h m (s m) = c h m (s' m)) → s = s') ∧
        ∀ fam : ∀ m : ℕ, ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}), (∀ m : ℕ, Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr
              (pow_dvd_pow (algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) (Nat.le_succ (m + 1)))) (fam (m + 1)) = fam m) →
          ((∃ s : ∀ m : ℕ, ↑((Ynr m).presheaf.obj (Opposite.op (U h m))),
              (∀ (m : ℕ) (hle : U h m ≤ (jnr m) ⁻¹ᵁ (U h (m + 1))),
              (Ynr m).presheaf.map (homOfLE hle).op (((jnr m).app (U h (m + 1))).hom (s (m + 1))) = s m) ∧
              ∀ m : ℕ, c h m (s m) = fam m) ↔
            ∀ (m : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra Onr B] [IsScalarTower 𝒪 Onr B],
              IsNilpotent (algebraMap 𝒪 B π) →
              ∀ (xbar xbar' : ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) →ₐ[Onr] B) (d d' P P' : DeligneDatum (K := K₀) π B),
                (d.line (stdFullLattice K₀) =
              Submodule.span B {(xbar (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
            d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
              (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (xbar (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) (chartERing.η Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
                (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
            d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
                (d'.line (stdFullLattice K₀) =
              Submodule.span B {(xbar' (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
            d'.line (FullLattice.act g₁ (stdFullLattice K₀)) =
              (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (xbar' (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) (chartERing.η Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
                (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
            d'.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
                DeligneDatum.IsPullback (K := K₀) (π := π) B h⁻¹ d P →
                DeligneDatum.IsPullback (K := K₀) (π := π) B h⁻¹ d' P' →
                (∃ γ ∈ Γ', DeligneDatum.IsPullback (K := K₀) (π := π) B (σ γ)⁻¹ P P') →
                xbar (fam m) = xbar' (fam m))

end FormalOmega
end CerednikDrinfeld

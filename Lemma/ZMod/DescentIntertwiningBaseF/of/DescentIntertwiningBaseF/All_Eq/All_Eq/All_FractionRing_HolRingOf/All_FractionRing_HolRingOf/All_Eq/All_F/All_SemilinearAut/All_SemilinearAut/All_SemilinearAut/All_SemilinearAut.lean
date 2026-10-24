import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_CerednikDrinfeld_DescentIntertwiningBase
import Lemma.Int.P2MUtil
set_option maxHeartbeats 999999
open scoped TensorProduct Quaternion NumberField MatrixGroups
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.Mumford CerednikDrinfeld.Omega AlgebraicCurve Int


/--
[CerednikDrinfeld_descentIntertwiningBase_of_towerIso](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CerednikDrinfeld_descentIntertwiningBase_of_towerIso.lean)
-/
@[path]
private lemma main
  [Field F₀] [Algebra (AlgebraicClosure ℚ) F₀]
  {A : ValuationSubring (AlgebraicClosure ℚ)} [Fact (A.DecompositionIsometric ℚ)] [DecidableEq A.valuation.Completion]
  {q q' r : ℕ}
  {ir irbar : Fin 2}
  {a b : ℚ}
  {ρ : ℍ[ℚ, a, b]ˣ →* Matrix.ProjGenLinGroup (Fin 2) ↥(ValuationSubring.ratClosure A)}
  {ϖ : Omega.PseudoUniformizer ↥(ValuationSubring.ratClosure A) A.valuation.Completion} [IsDomain (Omega.HolRingOf ϖ ρ)]
  {Γ : HeckeTower.Obj q q' → Subgroup ℍ[ℚ, a, b]ˣ}
  {w wbar : HeckeTower.Obj q q' → ℍ[ℚ, a, b]ˣ}
  {s : HeckeTower.AwayPrime q q' → ℍ[ℚ, a, b]ˣ}
  {dIso : ↥(A.decompositionSubgroup ℚ) →* Omega.IsometricAut ↥(ValuationSubring.ratClosure A) A.valuation.Completion}
  {gal₀ : ↥(A.decompositionSubgroup ℚ) →* SemilinearAut (AlgebraicClosure ℚ) F₀}
  {W : Fin 2 → SemilinearAut (AlgebraicClosure ℚ) F₀}
  {χ : ↥(A.decompositionSubgroup ℚ) →* Multiplicative (ZMod 2)}
  {𝕋 𝕋' : HeckeTower.TowerData q q' F₀}
-- given
  (galT : ∀ ℓ : HeckeTower.AwayPrime q q', ↥(A.decompositionSubgroup ℚ) →* SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
  (WT : ∀ ℓ : HeckeTower.AwayPrime q q', Fin 2 → SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
  (galT' : ∀ ℓ : HeckeTower.AwayPrime q q', ↥(A.decompositionSubgroup ℚ) →* SemilinearAut (AlgebraicClosure ℚ) (𝕋'.F ℓ))
  (WT' : ∀ ℓ : HeckeTower.AwayPrime q q', Fin 2 → SemilinearAut (AlgebraicClosure ℚ) (𝕋'.F ℓ))
  (θ : ∀ ℓ : HeckeTower.AwayPrime q q', 𝕋.F ℓ ≃ₐ[AlgebraicClosure ℚ] 𝕋'.F ℓ)
  (hθ : ∀ (α : HeckeTower.Arr q q') (x : F₀), θ α.1 (𝕋.φ α x) = 𝕋'.φ α x)
  (ιM' : ∀ j : HeckeTower.Obj q q', 𝕋'.objField j →+* FractionRing (Omega.HolRingOf ϖ ρ))
  (ιM : ∀ j : HeckeTower.Obj q q', 𝕋.objField j →+* FractionRing (Omega.HolRingOf ϖ ρ))
  (hι₀ : ∀ x : F₀, ιM none x = ιM' none x)
  (hιℓ : ∀ (ℓ : HeckeTower.AwayPrime q q') (x : 𝕋.F ℓ), ιM (some ℓ) x = ιM' (some ℓ) (θ ℓ x))
  (hBase : CerednikDrinfeld.DescentIntertwiningBase r ir irbar A ρ ϖ Γ w wbar s dIso F₀ 𝕋' gal₀ galT' W WT' χ ιM') :
-- imply
  CerednikDrinfeld.DescentIntertwiningBase r ir irbar A ρ ϖ Γ w wbar s dIso F₀ 𝕋 gal₀ galT W WT χ ιM := by
-- proof
  obtain ⟨p1, p2, p3, i0a, i0b, i0c, i1, i2a, i2b, i3a, i3b⟩ := hBase
  have hfun : (fun x : F₀ => ιM none x) = fun x => ιM' none x := funext hι₀
  refine ⟨p1, p2, p3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro z
    rw [hι₀]
    exact i0a z
  ·
    have hr : Set.range (ιM none) = Set.range (ιM' none) := by
      ext y; simp only [Set.mem_range, hι₀]
    rwa [hr]
  ·
    intro t ht
    have : (fun x : t => ιM none (x : 𝕋.objField none)) = fun x : t => ιM' none (x : 𝕋'.objField none) :=
      funext fun x => hι₀ x
    rw [this]; exact i0c t ht
  ·
    intro τ x
    rw [hι₀, hι₀]
    exact i1 τ x
  ·
    intro x
    rw [hι₀, hι₀]
    exact i2a x
  ·
    intro x
    rw [hι₀, hι₀]
    exact i2b x
  ·
    intro ℓ x
    rw [hιℓ, hθ (ℓ, 0) x, hι₀]
    exact i3a ℓ x
  ·
    intro ℓ x
    rw [hιℓ, hθ (ℓ, 1) x, hι₀]
    exact i3b ℓ x


-- created on 2026-10-24

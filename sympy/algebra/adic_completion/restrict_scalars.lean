import Mathlib.RingTheory.AdicCompletion.Algebra

universe u₁ u₂

namespace AdicCompletion

variable {A : Type u₁} [CommRing A] (B : Type u₂) [CommRing B] [Algebra A B] (𝔭 : Ideal A)

theorem restrictScalars_map_pow_smul_top (n : ℕ) :
    (((𝔭.map (algebraMap A B)) ^ n • ⊤ : Submodule B B).restrictScalars A) =
      (𝔭 ^ n • ⊤ : Submodule A B) := by
  rw [← Ideal.map_pow, Submodule.restrictScalars_map_smul_eq, Submodule.restrictScalars_top]

noncomputable def levelRestrictScalarsEquiv (n : ℕ) :
    (B ⧸ ((𝔭.map (algebraMap A B)) ^ n • ⊤ : Submodule B B)) ≃ₗ[A]
      B ⧸ (𝔭 ^ n • ⊤ : Submodule A B) :=
  (Submodule.Quotient.restrictScalarsEquiv A _).symm.trans
    (Submodule.quotEquivOfEq _ _ (restrictScalars_map_pow_smul_top B 𝔭 n))

theorem levelRestrictScalarsEquiv_mk (n : ℕ) (b : B) :
    levelRestrictScalarsEquiv B 𝔭 n (Submodule.Quotient.mk b) = Submodule.Quotient.mk b :=
  rfl

theorem transitionMap_levelRestrictScalarsEquiv {m n : ℕ} (hmn : m ≤ n)
    (y : B ⧸ ((𝔭.map (algebraMap A B)) ^ n • ⊤ : Submodule B B)) :
    transitionMap 𝔭 B hmn (levelRestrictScalarsEquiv B 𝔭 n y) =
      levelRestrictScalarsEquiv B 𝔭 m
        (transitionMap (𝔭.map (algebraMap A B)) B hmn y) :=
  Quotient.inductionOn' y fun _ => rfl

noncomputable def restrictScalarsEquiv :
    AdicCompletion (𝔭.map (algebraMap A B)) B ≃ₗ[A] AdicCompletion 𝔭 B where
  toFun x := ⟨fun n => levelRestrictScalarsEquiv B 𝔭 n (x.val n), fun {m n} hmn => by
    show transitionMap 𝔭 B hmn (levelRestrictScalarsEquiv B 𝔭 n (x.val n)) =
      levelRestrictScalarsEquiv B 𝔭 m (x.val m)
    rw [← x.prop hmn]
    exact transitionMap_levelRestrictScalarsEquiv B 𝔭 hmn (x.val n)⟩
  invFun y := ⟨fun n => (levelRestrictScalarsEquiv B 𝔭 n).symm (y.val n), fun {m n} hmn => by
    show transitionMap (𝔭.map (algebraMap A B)) B hmn
        ((levelRestrictScalarsEquiv B 𝔭 n).symm (y.val n)) =
      (levelRestrictScalarsEquiv B 𝔭 m).symm (y.val m)
    rw [← y.prop hmn, LinearEquiv.eq_symm_apply,
      ← transitionMap_levelRestrictScalarsEquiv B 𝔭 hmn
        ((levelRestrictScalarsEquiv B 𝔭 n).symm (y.val n)),
      LinearEquiv.apply_symm_apply]⟩
  map_add' x y := by
    ext n
    exact map_add (levelRestrictScalarsEquiv B 𝔭 n) _ _
  map_smul' a x := by
    ext n
    exact map_smul (levelRestrictScalarsEquiv B 𝔭 n) a _
  left_inv x := by
    ext n
    exact (levelRestrictScalarsEquiv B 𝔭 n).symm_apply_apply _
  right_inv y := by
    ext n
    exact (levelRestrictScalarsEquiv B 𝔭 n).apply_symm_apply _

theorem restrictScalarsEquiv_of (b : B) :
    restrictScalarsEquiv B 𝔭 (of (𝔭.map (algebraMap A B)) B b) = of 𝔭 B b := by
  ext n
  rfl

theorem restrictScalarsEquiv_symm_of (b : B) :
    (restrictScalarsEquiv B 𝔭).symm (of 𝔭 B b) = of (𝔭.map (algebraMap A B)) B b := by
  ext n
  rfl

end AdicCompletion

set_option pp.universes true in
#check @AdicCompletion.restrictScalarsEquiv

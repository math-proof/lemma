import Mathlib
import sympy.Basic
import sympy.algebra.direct_limit
open scoped TensorProduct


private lemma map_id_eq_rTensor
  {R₀ : Type*} [CommRing R₀] {A A' : Type*} [CommRing A] [CommRing A']
  [Algebra R₀ A] [Algebra R₀ A']
  (B : Type*) [CommRing B] [Algebra R₀ B]
  (φ : A →ₐ[R₀] A') (x : A ⊗[R₀] B) :
    Algebra.TensorProduct.map φ (AlgHom.id R₀ B) x = LinearMap.rTensor B φ.toLinearMap x := by
  refine TensorProduct.inductionOn x ?_ ?_
  ·
    intro a b
    simp [Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul]
  ·
    intro x y hx hy
    rw [map_add, map_add, hx, hy]


/--
[Algebra_TensorProduct_isDirectLimit_map_of_isDirectLimit](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_TensorProduct_isDirectLimit_map_of_isDirectLimit.lean)
-/
@[path]
private lemma main
  {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
  {R₀ : Type v} [CommRing R₀]
  {G : ι → Type w} [∀ i, CommRing (G i)] [∀ i, Algebra R₀ (G i)]
  {f : ∀ i j : ι, i ≤ j → G i →ₐ[R₀] G j} [DirectedSystem G fun i j h => ⇑(f i j h)]
  {R : Type w} [CommRing R] [Algebra R₀ R] [∀ i, Algebra (G i) R] [∀ i, IsScalarTower R₀ (G i) R]
  {B : Type w} [CommRing B] [Algebra R₀ B]
-- given
  (hR : IsDirectLimit (fun i j h => ⇑(f i j h)) fun i => ⇑(algebraMap (G i) R)) :
-- imply
  ∃ _ : DirectedSystem (fun i => G i ⊗[R₀] B) (fun i j h => ⇑(Algebra.TensorProduct.map (f i j h) (AlgHom.id R₀ B))),
    IsDirectLimit (fun i j h => ⇑(Algebra.TensorProduct.map (f i j h) (AlgHom.id R₀ B)))
      (fun i => ⇑(Algebra.TensorProduct.map (IsScalarTower.toAlgHom R₀ (G i) R)
        (AlgHom.id R₀ B))) := by
-- proof
  classical
  have : DecidableEq ι := Classical.decEq ι
  have hDS : DirectedSystem (fun i => G i ⊗[R₀] B)
      (fun i j h => ⇑(Algebra.TensorProduct.map (f i j h) (AlgHom.id R₀ B))) := by
    constructor
    ·
      intro i x
      refine TensorProduct.inductionOn x ?_ ?_
      ·
        intro a b
        rw [Algebra.TensorProduct.map_tmul, DirectedSystem.map_self' (fun i j h => f i j h)]
        rfl
      ·
        intro x y hx hy
        rw [map_add, hx, hy]
    ·
      intro k j i hij hjk x
      refine TensorProduct.inductionOn x ?_ ?_
      ·
        intro a b
        rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
          Algebra.TensorProduct.map_tmul, DirectedSystem.map_map' (fun i j h => f i j h)]
        rfl
      ·
        intro x y hx hy
        simp only [map_add, hx, hy]
  refine ⟨hDS, ?_⟩
  have hcompat : ∀ i j (hij : i ≤ j) (x : G i ⊗[R₀] B),
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom R₀ (G j) R) (AlgHom.id R₀ B)
        (Algebra.TensorProduct.map (f i j hij) (AlgHom.id R₀ B) x) =
        Algebra.TensorProduct.map (IsScalarTower.toAlgHom R₀ (G i) R) (AlgHom.id R₀ B) x := by
    intro i j hij x
    refine TensorProduct.inductionOn x ?_ ?_
    ·
      intro a b
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.toAlgHom_apply]
      rw [hR.compatibility]
    ·
      intro x y hx hy
      simp only [map_add, hx, hy]
  let fL : ∀ i j : ι, i ≤ j → G i →ₗ[R₀] G j := fun i j h => (f i j h).toLinearMap
  have hDSL : DirectedSystem G (fun i j h => ⇑(fL i j h)) :=
    ‹DirectedSystem G fun i j h => ⇑(f i j h)›
  have hR' : IsDirectLimit (fun i j h => ⇑(fL i j h))
      (fun i => ⇑((IsScalarTower.toAlgHom R₀ (G i) R).toLinearMap)) := hR
  let gLim : ∀ i, G i →ₗ[R₀] Module.DirectLimit G fL := fun i =>
    Module.DirectLimit.of R₀ ι G fL i
  let gR : ∀ i, G i →ₗ[R₀] R := fun i => (IsScalarTower.toAlgHom R₀ (G i) R).toLinearMap
  let phi : Module.DirectLimit G fL →ₗ[R₀] R :=
    Module.DirectLimit.lift R₀ ι G fL gR (fun i j hij x => hR.compatibility i j hij x)
  let e : Module.DirectLimit G fL ≃ R :=
    IsDirectLimit.Equiv (fun i j h => ⇑(fL i j h)) (fun i => ⇑(gLim i)) (fun i => ⇑(gR i))
  have hfun : (phi : Module.DirectLimit G fL → R) = e := by
    ext z
    obtain ⟨i, x, hx⟩ := Module.DirectLimit.exists_of (R := R₀) (ι := ι) (G := G) (f := fL) z
    rw [← hx]
    have hlift : phi (Module.DirectLimit.of R₀ ι G fL i x) = gR i x :=
      Module.DirectLimit.lift_of (R := R₀) (ι := ι) (G := G) (f := fL) (g := gR)
        (Hg := fun i j hij y => hR.compatibility i j hij y) (x := x)
    have he : e (⇑(gLim i) x) = ⇑(gR i) x :=
      IsDirectLimit.Equiv_apply (fun i j h => ⇑(fL i j h)) (fun i => ⇑(gLim i))
        (fun i => ⇑(gR i)) i x
    rw [hlift]
    simpa [gLim] using he.symm
  have hbij : Function.Bijective phi := by
    rw [hfun]
    apply e.bijective
  let Φ : Module.DirectLimit G fL ≃ₗ[R₀] R := LinearEquiv.ofBijective phi hbij
  have hΦsymm : ∀ i (a : G i), Φ.symm ((IsScalarTower.toAlgHom R₀ (G i) R) a) =
      Module.DirectLimit.of R₀ ι G fL i a := by
    intro i a
    rw [LinearEquiv.symm_apply_eq]
    simp [Φ, phi, LinearEquiv.ofBijective_apply]
    exact (Module.DirectLimit.lift_of (R := R₀) (ι := ι) (G := G) (f := fL)
      (g := gR) (Hg := fun i j hij x => hR.compatibility i j hij x) (x := a)).symm
  let Ψ : R ⊗[R₀] B ≃ₗ[R₀] Module.DirectLimit (fun i => G i ⊗[R₀] B)
      (fun i j h => LinearMap.rTensor B (fL i j h)) :=
    (TensorProduct.congr Φ.symm (LinearEquiv.refl R₀ B)).trans
      (TensorProduct.directLimitLeft fL B)
  have hΨ : ∀ i (x : G i ⊗[R₀] B),
      Ψ (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R₀ (G i) R) (AlgHom.id R₀ B) x) =
        Module.DirectLimit.of R₀ ι (fun i => G i ⊗[R₀] B)
          (fun i j h => LinearMap.rTensor B (fL i j h)) i x := by
    intro i x
    refine TensorProduct.inductionOn x ?_ ?_
    ·
      intro a b
      simp only [Ψ, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, LinearEquiv.trans_apply,
        TensorProduct.congr_tmul, LinearEquiv.refl_apply]
      rw [hΦsymm, TensorProduct.directLimitLeft_tmul_of]
    ·
      intro x y hx hy
      simp only [map_add, hx, hy]
  constructor
  ·
    intro z
    refine TensorProduct.inductionOn z ?_ ?_
    ·
      intro r b
      obtain ⟨i, a, ha⟩ := hR.surj r
      exact ⟨i, a ⊗ₜ b, by simp [Algebra.TensorProduct.map_tmul, ha]⟩
    ·
      intro x y hx hy
      obtain ⟨i, xi, hxi⟩ := hx
      obtain ⟨j, yj, hyj⟩ := hy
      obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
      refine ⟨k, Algebra.TensorProduct.map (f i k hik) (AlgHom.id R₀ B) xi +
        Algebra.TensorProduct.map (f j k hjk) (AlgHom.id R₀ B) yj, ?_⟩
      rw [map_add, hcompat, hcompat, hxi, hyj]
  ·
    intro i j xi yj h
    have h' := congrArg Ψ h
    rw [hΨ, hΨ] at h'
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
    rw [← Module.DirectLimit.of_f (hij := hik), ← Module.DirectLimit.of_f (hij := hjk)] at h'
    obtain ⟨l, hkl, hl⟩ := Module.DirectLimit.exists_eq_of_of_eq h'
    refine ⟨l, hik.trans hkl, hjk.trans hkl, ?_⟩
    rw [← hDS.map_map hik hkl, ← hDS.map_map hjk hkl]
    show Algebra.TensorProduct.map (f k l hkl) (AlgHom.id R₀ B)
      (Algebra.TensorProduct.map (f i k hik) (AlgHom.id R₀ B) xi) =
      Algebra.TensorProduct.map (f k l hkl) (AlgHom.id R₀ B)
        (Algebra.TensorProduct.map (f j k hjk) (AlgHom.id R₀ B) yj)
    simp only [map_id_eq_rTensor]
    exact hl
  ·
    intro i j hij x
    exact hcompat i j hij x


-- created on 2026-10-16

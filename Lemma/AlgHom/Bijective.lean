import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped TensorProduct


/--
[Algebra_TensorProduct_bijective_productMap_pi_comp_of_isGalois](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_TensorProduct_bijective_productMap_pi_comp_of_isGalois.lean)
-/
@[path]
private lemma main
  [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  [Field F] [Algebra K F]
  {σ₀ : L →ₐ[K] F} :
-- imply
  Function.Bijective
    (Algebra.TensorProduct.productMap
      (AlgHom.pi (fun τ : L ≃ₐ[K] L => σ₀.comp (τ : L →ₐ[K] L)))
      (AlgHom.pi (fun _ : L ≃ₐ[K] L => AlgHom.id K F))) := by
-- proof
  classical
  set n := Module.finrank K L with hn
  let b : Module.Basis (Fin n) K L := Module.finBasis K L
  let G := L ≃ₐ[K] L
  let C := G → F
  let gL : L →ₐ[K] C := AlgHom.pi (fun τ : G => σ₀.comp (τ : L →ₐ[K] L))
  let gF : F →ₐ[K] C := AlgHom.pi (fun _ : G => AlgHom.id K F)
  let Φ : L ⊗[K] F →ₐ[K] C := Algebra.TensorProduct.productMap gL gF
  let gFF : F →ₐ[F] C := AlgHom.pi (fun _ : G => AlgHom.id F F)
  let ψ : F ⊗[K] L →ₐ[F] C := Algebra.TensorProduct.productLeftAlgHom gFF gL
  have hcomm : ∀ z, Φ z = ψ (Algebra.TensorProduct.comm K L F z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul ℓ f =>
      ext τ
      rw [Algebra.TensorProduct.productMap_apply_tmul, Algebra.TensorProduct.comm_tmul,
        Algebra.TensorProduct.lift_tmul, Pi.mul_apply, Pi.mul_apply, AlgHom.pi_apply,
        AlgHom.pi_apply, AlgHom.pi_apply]
      simp [mul_comm]
    | add x y hx hy =>
      simp [Φ, ψ, hx, hy]
  let bF : Module.Basis (Fin n) F (F ⊗[K] L) := Algebra.TensorProduct.basis F b
  let M : Matrix G (Fin n) F := fun τ i => σ₀ (τ (b i))
  have hψbasis : ∀ i τ, ψ (bF i) τ = M τ i := by
    intro i τ
    rw [Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.lift_tmul, Pi.mul_apply,
      AlgHom.pi_apply, AlgHom.pi_apply, map_one, one_mul, AlgHom.comp_apply]
    rfl
  have hψ : ∀ z : F ⊗[K] L, ψ z = M.mulVec (fun i => bF.repr z i) := by
    intro z
    conv_lhs => rw [← bF.sum_repr z]
    ext τ
    rw [map_sum, Finset.sum_apply, Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hsmul : ψ (bF.repr z i • bF i) = bF.repr z i • ψ (bF i) :=
      ψ.toLinearMap.map_smul (bF.repr z i) (bF i)
    rw [hsmul, Pi.smul_apply, hψbasis, smul_eq_mul, mul_comm]
  have hinj_comp : Function.Injective (fun τ : G => σ₀.comp (τ : L →ₐ[K] L)) := by
    intro τ τ' h
    apply AlgEquiv.ext
    intro x
    apply σ₀.toRingHom.injective
    apply congrArg (fun φ : L →ₐ[K] F => φ x) h
  have hrows : LinearIndependent F (fun τ : G => M τ) := by
    rw [linearIndependent_iff']
    intro s g hg τ hτ
    have hind := (linearIndependent_toLinearMap K L F).comp _ hinj_comp
    rw [linearIndependent_iff'] at hind
    refine hind s g ?_ τ hτ
    apply b.ext
    intro i
    have hi := congrFun hg i
    rw [Finset.sum_apply] at hi
    simp only [Pi.smul_apply, smul_eq_mul] at hi
    rw [LinearMap.zero_apply, LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, Function.comp_apply, AlgHom.toLinearMap_apply, AlgHom.coe_comp,
      smul_eq_mul]
    apply hi
  have hcard : Fintype.card G = n := by
    rw [hn, ← IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card]
  let e : G ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let M' : Matrix (Fin n) (Fin n) F := fun k i => M (e.symm k) i
  have hrows' : LinearIndependent F M'.row := by
    show LinearIndependent F (fun k : Fin n => M (e.symm k))
    apply hrows.comp e.symm e.symm.injective
  have hU : IsUnit M' := Matrix.linearIndependent_rows_iff_isUnit.mp hrows'
  have hMM' : ∀ c : Fin n → F, M.mulVec c = (M'.mulVec c) ∘ e := by
    intro c
    funext τ
    simp only [Function.comp_apply, Matrix.mulVec, dotProduct, M', Equiv.symm_apply_apply]
  have hinj : Function.Injective ψ := by
    intro z₁ z₂ h
    have h' : M'.mulVec (fun i => bF.repr z₁ i) = M'.mulVec (fun i => bF.repr z₂ i) := by
      have h0 : M.mulVec (fun i => bF.repr z₁ i) = M.mulVec (fun i => bF.repr z₂ i) := by
        rw [← hψ, ← hψ, h]
      rw [hMM', hMM'] at h0
      funext k
      have := congrFun h0 (e.symm k)
      simpa using this
    have h'' := Matrix.mulVec_injective_of_isUnit hU h'
    apply bF.repr.injective
    ext i
    apply congrFun h'' i
  have hdim : Module.finrank F (F ⊗[K] L) = Module.finrank F C := by
    rw [Module.finrank_eq_card_basis bF, Module.finrank_fintype_fun_eq_card, Fintype.card_fin, hn,
      ← IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card]
  have hsurj : Function.Surjective ψ.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  have hψbij : Function.Bijective ψ := ⟨hinj, hsurj⟩
  have hfun : (Φ : L ⊗[K] F → C) = ψ ∘ Algebra.TensorProduct.comm K L F := by
    funext z
    apply hcomm
  show Function.Bijective Φ
  rw [hfun]
  apply Function.Bijective.comp hψbij (Algebra.TensorProduct.comm K L F).bijective


-- created on 2026-10-16

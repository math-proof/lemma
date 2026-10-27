import Mathlib
import Initialize.Tactic.Attr.Basic
open AdicCompletion Function
open scoped TensorProduct


private lemma isAdicComplete_pi_of_fintype
  {R : Type u} [CommRing R] (I : Ideal R) (ι : Type) [Fintype ι] [DecidableEq ι]
-- given
  [IsAdicComplete I R] :
-- imply
  IsAdicComplete I (ι → R) := by
-- proof
  rw [← AdicCompletion.of_bijective_iff]
  let e1 : (ι → R) ≃ₗ[R] R ⊗[R] (ι → R) := (TensorProduct.lid R (ι → R)).symm
  let e2 : R ⊗[R] (ι → R) ≃ₗ[R] AdicCompletion I R ⊗[R] (ι → R) :=
    LinearEquiv.rTensor (ι → R) (AdicCompletion.ofLinearEquiv I R)
  let e3 : AdicCompletion I R ⊗[R] (ι → R) →ₗ[R] AdicCompletion I (ι → R) :=
    (AdicCompletion.ofTensorProduct I (ι → R)).restrictScalars R
  have he3 : Bijective e3 := AdicCompletion.ofTensorProduct_bijective_of_pi_of_fintype I ι
  have : (of I (ι → R) : (ι → R) → _) = e3 ∘ e2 ∘ e1 := by
    funext x
    simp [e1, e2, e3, Function.comp_apply, TensorProduct.lid_symm_apply, LinearEquiv.rTensor_tmul,
      ofLinearEquiv_apply, ofTensorProduct_tmul]
    have h1 : (of I R) 1 = 1 := by
      have := (AdicCompletion.algebraMap_apply (S := R) (I := I) (1 : R)).symm
      rw [map_one] at this
      simp at this
      apply this
    rw [h1, one_smul]
  rw [this]
  apply he3.comp (e2.bijective.comp e1.bijective)


private lemma isAdicComplete_of_linearEquiv
  {R : Type u} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {I : Ideal R}
  (e : M ≃ₗ[R] N)
-- given
  [IsAdicComplete I M] :
-- imply
  IsAdicComplete I N := by
-- proof
  rw [← AdicCompletion.of_bijective_iff]
  have h : (of I N : N → _) = (AdicCompletion.congr I e) ∘ (of I M) ∘ e.symm := by
    funext x
    simp [AdicCompletion.congr_apply, map_of]
  rw [h]
  apply (AdicCompletion.congr I e).bijective.comp ((AdicCompletion.of_bijective I M).comp e.symm.bijective)


private lemma isAdicComplete_of_finite_of_free
  {R : Type u} [CommRing R] (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Free R M]
-- given
  [IsAdicComplete I R] :
-- imply
  IsAdicComplete I M := by
-- proof
  classical
  let b := Module.Free.chooseBasis R M
  have : Fintype (Module.Free.ChooseBasisIndex R M) := Module.Free.ChooseBasisIndex.fintype R M
  let n := Fintype.card (Module.Free.ChooseBasisIndex R M)
  let σ : Module.Free.ChooseBasisIndex R M ≃ Fin n := Fintype.equivFin _
  let b' : Module.Basis (Fin n) R M := b.reindex σ
  have := isAdicComplete_pi_of_fintype I (Fin n)
  apply isAdicComplete_of_linearEquiv b'.equivFun.symm


private noncomputable abbrev red
  {𝓞 : Type u} [CommRing 𝓞]
  {k : Type v} [CommRing k] [Algebra 𝓞 k]
  {Y : Type w'} [CommRing Y] [Algebra 𝓞 Y] :
  Y →ₐ[𝓞] k ⊗[𝓞] Y :=
  Algebra.TensorProduct.includeRight


private lemma red_apply
  {𝓞 : Type u} [CommRing 𝓞]
  {k : Type v} [CommRing k] [Algebra 𝓞 k]
  {Y : Type w'} [CommRing Y] [Algebra 𝓞 Y] (y : Y) :
-- imply
  red (𝓞 := 𝓞) (k := k) (Y := Y) y = (1 : k) ⊗ₜ[𝓞] y := rfl


private lemma red_surjective
  {𝓞 : Type u} [CommRing 𝓞]
  {k : Type v} [CommRing k] [Algebra 𝓞 k]
  {Y : Type w'} [CommRing Y] [Algebra 𝓞 Y]
-- given
  (hk : Surjective (algebraMap 𝓞 k)) :
-- imply
  Surjective (red (𝓞 := 𝓞) (k := k) (Y := Y)) := by
-- proof
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul a r =>
    obtain ⟨o, rfl⟩ := hk a
    refine ⟨o • r, ?_⟩
    rw [red_apply, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.algebraMap_eq_smul_one]
  | add x y hx hy =>
    obtain ⟨r, rfl⟩ := hx
    obtain ⟨s, rfl⟩ := hy
    refine ⟨r + s, ?_⟩
    apply map_add


private lemma ker_red
  {𝓞 : Type u} [CommRing 𝓞]
  {k : Type v} [CommRing k] [Algebra 𝓞 k]
  {Y : Type w'} [CommRing Y] [Algebra 𝓞 Y]
-- given
  (hk : Surjective (algebraMap 𝓞 k)) :
-- imply
  RingHom.ker (red (𝓞 := 𝓞) (k := k) (Y := Y)) = (RingHom.ker (algebraMap 𝓞 k)).map (algebraMap 𝓞 Y) := by
-- proof
  set I := RingHom.ker (algebraMap 𝓞 k)
  apply le_antisymm
  ·
    let J : Ideal Y := I.map (algebraMap 𝓞 Y)
    have hle : RingHom.ker (algebraMap 𝓞 k) ≤ RingHom.ker ((Ideal.Quotient.mk J).comp (algebraMap 𝓞 Y)) := by
      intro o ho
      rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      apply Ideal.mem_map_of_mem _ ho
    let κ₀ : k →+* Y ⧸ J := (algebraMap 𝓞 k).liftOfSurjective hk ⟨_, hle⟩
    have hκ₀ : ∀ o, κ₀ (algebraMap 𝓞 k o) = Ideal.Quotient.mk J (algebraMap 𝓞 Y o) := fun o =>
      (algebraMap 𝓞 k).liftOfRightInverse_comp_apply _ _ ⟨_, hle⟩ o
    let κ : k →ₐ[𝓞] Y ⧸ J := ⟨κ₀, fun o => (hκ₀ o).trans rfl⟩
    let Ψ : k ⊗[𝓞] Y →ₐ[𝓞] Y ⧸ J :=
      Algebra.TensorProduct.lift κ (Ideal.Quotient.mkₐ 𝓞 J) fun _ _ => Commute.all _ _
    intro r hr
    rw [RingHom.mem_ker] at hr
    have : Ψ ((1 : k) ⊗ₜ[𝓞] r) = Ideal.Quotient.mk J r := by
      rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      rfl
    rw [← red_apply, hr, _root_.map_zero] at this
    apply Ideal.Quotient.eq_zero_iff_mem.1 this.symm
  ·
    rw [Ideal.map_le_iff_le_comap]
    intro o ho
    rw [RingHom.mem_ker] at ho
    rw [Ideal.mem_comap, RingHom.mem_ker, red_apply, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one, ho, TensorProduct.zero_tmul]


private lemma algHom_ext_one_tmul
  {𝓞 : Type u} [CommRing 𝓞]
  {k : Type v} [CommRing k] [Algebra 𝓞 k]
  {X : Type w} [CommRing X] [Algebra 𝓞 X]
  {Y : Type w'} [CommRing Y] [Algebra 𝓞 Y]
  {f g : k ⊗[𝓞] X →ₐ[k] k ⊗[𝓞] Y}
-- given
  (h : ∀ r : X, f ((1 : k) ⊗ₜ[𝓞] r) = g ((1 : k) ⊗ₜ[𝓞] r)) :
-- imply
  f = g := by
-- proof
  refine Algebra.TensorProduct.ext' fun c r => ?_
  have hc : c ⊗ₜ[𝓞] r = c • ((1 : k) ⊗ₜ[𝓞] r) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hc, map_smul, map_smul, h]


/--
[Algebra_FormallySmooth_exists_algHom_baseChange_eq_of_isAdicComplete](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_FormallySmooth_exists_algHom_baseChange_eq_of_isAdicComplete.lean)
-/
@[path]
private lemma main
  {𝓞 : Type u} [CommRing 𝓞]
  {k : Type v} [CommRing k] [Algebra 𝓞 k]
  {ℛ : Type w} [CommRing ℛ] [Algebra 𝓞 ℛ] [Algebra.FormallySmooth 𝓞 ℛ]
  {Y : Type w'} [CommRing Y] [Algebra 𝓞 Y] [Module.Finite 𝓞 Y] [Module.Free 𝓞 Y]
  (p : ℕ) [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
  (χ : TensorProduct 𝓞 k ℛ →ₐ[k] TensorProduct 𝓞 k Y)
-- given
  (hk : Function.Surjective (algebraMap 𝓞 k))
  (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)}) :
-- imply
  ∃ x : ℛ →ₐ[𝓞] Y, Algebra.TensorProduct.map (AlgHom.id k k) x = χ := by
-- proof
  set J : Ideal Y := RingHom.ker (red (𝓞 := 𝓞) (k := k) (Y := Y)) with hJdef
  have hJ : J = (Ideal.span {(p : 𝓞)}).map (algebraMap 𝓞 Y) := by
    rw [hJdef, ker_red hk, hker]
  have : IsAdicComplete (Ideal.span {(p : 𝓞)}) Y := isAdicComplete_of_finite_of_free _ Y
  have : IsAdicComplete J Y := by
    rw [hJ]
    apply (IsAdicComplete.map_algebraMap_iff (Ideal.span {(p : 𝓞)}) (S := Y) (M := Y)).2 inferInstance
  let e : (Y ⧸ J) ≃ₐ[𝓞] k ⊗[𝓞] Y := Ideal.quotientKerAlgEquivOfSurjective (red_surjective hk)
  let χ' : ℛ →ₐ[𝓞] k ⊗[𝓞] Y := (χ.restrictScalars 𝓞).comp (red (𝓞 := 𝓞) (k := k) (Y := ℛ))
  let f : ℛ →ₐ[𝓞] Y ⧸ J := (e.symm : k ⊗[𝓞] Y →ₐ[𝓞] Y ⧸ J).comp χ'
  obtain ⟨x, hx⟩ := Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete (I := J) f
  refine ⟨x, algHom_ext_one_tmul fun r => ?_⟩
  have h1 : (Ideal.Quotient.mkₐ 𝓞 J) (x r) = f r := by
    rw [← hx]
    rfl
  have h2 : e ((Ideal.Quotient.mkₐ 𝓞 J) (x r)) = red (𝓞 := 𝓞) (k := k) (Y := Y) (x r) :=
    Ideal.quotientKerAlgEquivOfSurjective_mk (red_surjective hk) (x r)
  have h3 : e (f r) = χ' r := by
    show e (e.symm (χ' r)) = χ' r
    apply e.apply_symm_apply
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, ← red_apply, ← h2, h1, h3]
  rfl


-- created on 2026-10-16

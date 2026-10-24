import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.TensorProductDomain
open TensorProduct


/--
[algHomOfMaximalIdeal_ker](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TensorProductDomain.lean)
-/
@[path]
lemma algHomOfMaximalIdeal_ker
  [Field k]
  [IsAlgClosed k]
  {m : Ideal R}
  [hm : m.IsMaximal]
  {r : R} :
-- imply
  algHomOfMaximalIdeal k m r = 0 ↔ r ∈ m := by
-- proof
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType k (R ⧸ m) := Algebra.FiniteType.quotient k m
  haveI : Module.Finite k (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (R ⧸ m)
  haveI : Algebra.IsIntegral k (R ⧸ m) := Algebra.IsIntegral.of_finite k (R ⧸ m)
  unfold algHomOfMaximalIdeal
  simp only [AlgHom.coe_comp, AlgEquiv.coe_algHom, Function.comp_apply]
  constructor
  · intro h
    have hbij := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := R ⧸ m)
    let e := AlgEquiv.ofBijective (Algebra.ofId k (R ⧸ m)) hbij
    have heq : e (e.symm (IsScalarTower.toAlgHom k R (R ⧸ m) r)) = e 0 := congr_arg e h
    simp only [AlgEquiv.apply_symm_apply, map_zero] at heq
    simp only [IsScalarTower.toAlgHom, AlgHom.coe_mk, Ideal.Quotient.algebraMap_eq] at heq
    rwa [Ideal.Quotient.eq_zero_iff_mem] at heq
  · intro h
    simp only [IsScalarTower.toAlgHom, AlgHom.coe_mk,
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero]

/--
[coord_evalTensorMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TensorProductDomain.lean)
-/
@[path]
lemma coord_evalTensorMap
  [Field k]
  [IsAlgClosed k]
  {bS : Module.Basis ι k S}
  {φ : R →ₐ[k] k}
  {u : R ⊗[k] S}
  {i : ι} :
-- imply
  bS.repr (evalTensorMap φ u) i = φ ((Algebra.TensorProduct.basisAux R bS u) i) := by
-- proof
  induction u using TensorProduct.induction_on with
  | zero => simp [map_zero]
  | tmul r s =>
    have heval : evalTensorMap φ (r ⊗ₜ[k] s) = algebraMap k S (φ r) * s := by
      simp [evalTensorMap, Algebra.TensorProduct.productMap_apply_tmul, Algebra.ofId_apply]
    rw [heval, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
    rw [Algebra.TensorProduct.basisAux_tmul]
    simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.mapRange_apply]
    rw [map_mul, AlgHom.commutes]; simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
section MainTheorem
variable {k : Type*} [Field k] [IsAlgClosed k]

/--
[IsAffineAlgebra.tensorProduct](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TensorProductDomain.lean)
-/
@[path]
lemma IsAffineAlgebra.tensorProduct
  [Field k]
  [IsAlgClosed k]
  {R S : Type*}
  [CommRing R]
  [CommRing S]
  [Algebra k R]
  [Algebra k S]
  [IsAffineAlgebra k R]
  [IsAffineAlgebra k S] :
-- imply
  IsAffineAlgebra k (R ⊗[k] S) where finiteType :=
-- proof
  Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType k R)
    (Algebra.FiniteType.baseChange R)
  isDomain := by
    haveI : Nontrivial (R ⊗[k] S) :=
      Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain k R S
        (RingHom.injective _) (RingHom.injective _)
    haveI : NoZeroDivisors (R ⊗[k] S) := by
      constructor
      intro u v huv
      classical
      let bS := Module.Free.chooseBasis k S
      let B := Algebra.TensorProduct.basisAux R bS
      have key : ∀ (J : Ideal R) [J.IsMaximal],
        (∀ i, (B u) i ∈ J) ∨ (∀ i, (B v) i ∈ J) := by
        intro J hJ
        have h0 : evalTensorMap (algHomOfMaximalIdeal k J) (u * v) = 0 := by
          rw [huv, map_zero]
        rw [map_mul] at h0
        obtain hhu | hhv := mul_eq_zero.mp h0
        · left; intro i
          have := congr_arg (bS.repr · i) hhu
          simp only [map_zero, Finsupp.zero_apply] at this
          rw [coord_evalTensorMap] at this
          exact (algHomOfMaximalIdeal_ker J _).mp this
        · right; intro i
          have := congr_arg (bS.repr · i) hhv
          simp only [map_zero, Finsupp.zero_apply] at this
          rw [coord_evalTensorMap] at this
          exact (algHomOfMaximalIdeal_ker J _).mp this
      haveI : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := k)
      have hjac : (⊥ : Ideal R).jacobson = ⊥ :=
        (inferInstance : IsJacobsonRing R).out Ideal.isRadical_bot_of_noZeroDivisors
      have hab_zero : ∀ i j, (B u) i * (B v) j = 0 := by
        intro i j
        have h_mem : (B u) i * (B v) j ∈ (⊥ : Ideal R).jacobson := by
          rw [Ideal.jacobson, Submodule.mem_sInf]
          intro J ⟨_, hJmax⟩
          obtain hu_sub | hv_sub := @key J hJmax
          · exact Ideal.mul_mem_right _ _ (hu_sub i)
          · exact Ideal.mul_mem_left _ _ (hv_sub j)
        rwa [hjac, Ideal.mem_bot] at h_mem
      by_contra h
      push Not at h
      obtain ⟨hu, hv⟩ := h
      have hBu : B u ≠ 0 := fun h0 => hu (B.map_eq_zero_iff.mp h0)
      obtain ⟨i₀, hi₀⟩ := Finsupp.ne_iff.mp hBu
      simp only [Finsupp.zero_apply] at hi₀
      have hBv : B v = 0 := by
        ext j; simp only [Finsupp.zero_apply]
        exact (mul_eq_zero.mp (hab_zero i₀ j)).resolve_left hi₀
      exact hv (B.map_eq_zero_iff.mp hBv)
    exact NoZeroDivisors.to_isDomain (R ⊗[k] S)
end MainTheorem


-- created on 2026-10-23

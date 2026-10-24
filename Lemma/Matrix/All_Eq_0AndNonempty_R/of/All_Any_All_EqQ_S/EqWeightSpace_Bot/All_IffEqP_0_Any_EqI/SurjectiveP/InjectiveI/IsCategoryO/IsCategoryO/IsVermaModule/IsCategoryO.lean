import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.LieGroups.code.ExtVanishingKernelZero


/--
[CategoryO.ext_vanishing_kernel_zero_and_iso](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ExtVanishingKernelZero.lean)
-/
@[path]
lemma CategoryO.ext_vanishing_kernel_zero_and_iso
  [Field R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {ci : CartanInvolution rd}
  {wg : WeylGroupData Δ}
  {E : Type uCatO}
  [AddCommGroup E]
  [Module R E]
  [LieRingModule 𝔤 E]
  [LieModule R 𝔤 E]
  [Module.Finite R E]
  [LieModule.IsTrivial 𝔤 E]
  {Mlam : Type uCatO}
  [AddCommGroup Mlam]
  [Module R Mlam]
  [LieRingModule 𝔤 Mlam]
  [LieModule R 𝔤 Mlam]
  {lam : Δ.𝔥 →ₗ[R] R}
  {K : Type uCatO}
  [AddCommGroup K]
  [Module R K]
  [LieRingModule 𝔤 K]
  [LieModule R 𝔤 K]
  {Z : Type uCatO}
  [AddCommGroup Z]
  [Module R Z]
  [LieRingModule 𝔤 Z]
  [LieModule R 𝔤 Z]
  {i : K →ₗ⁅R, 𝔤⁆ (TensorProduct R E Mlam)}
  {p : (TensorProduct R E Mlam) →ₗ⁅R, 𝔤⁆ Z}
-- given
  (hMlamO : IsCategoryO Δ rd Mlam)
  (hMlam_verma : IsVermaModule Δ Mlam lam)
  (hKO : IsCategoryO Δ rd K)
  (hZO : IsCategoryO Δ rd Z)
  (hi : Function.Injective i)
  (hp : Function.Surjective p)
  (hexact : ∀ (m : TensorProduct R E Mlam), p m = 0 ↔ ∃ k : K, i k = m)
  (hK_lam : WeightSpace Δ K lam = ⊥)
  (hExtZ : ∀ (mu : Δ.𝔥 →ₗ[R] R) (MmuDual : Type uCatO) [AddCommGroup MmuDual] [Module R MmuDual] [LieRingModule 𝔤 MmuDual] [LieModule R 𝔤 MmuDual] (hMmuDualO : IsCategoryO Δ rd MmuDual) (_ : IsContragredientVerma rd MmuDual mu hMmuDualO) (E' : Type uCatO) [AddCommGroup E'] [Module R E'] [LieRingModule 𝔤 E'] [LieModule R 𝔤 E'] (_ : IsCategoryO Δ rd E') (j : MmuDual →ₗ⁅R, 𝔤⁆ E') (_ : Function.Injective j) (q : E' →ₗ⁅R, 𝔤⁆ Z) (_ : Function.Surjective q), ∃ (s : Z →ₗ⁅R, 𝔤⁆ E'), ∀ z, q (s z) = z) :
-- imply
  (∀ (k : K), k = 0) ∧ Nonempty (Z ≃ₗ⁅R, 𝔤⁆ (TensorProduct R E Mlam)) := by
-- proof
  have hK_zero : ∀ (k : K), k = 0 :=
    lemma_20_4_kernel_zero ci (wg := wg) hMlamO lam hMlam_verma hKO hZO i hi p hp
      hexact hK_lam hExtZ
  constructor
  ·
    exact hK_zero
  ·
    have hp_inj : Function.Injective p := by
      intro m₁ m₂ h
      have hpm : p (m₁ - m₂) = 0 := by rw [map_sub]; exact sub_eq_zero.mpr h
      rw [hexact] at hpm
      obtain ⟨k, hk⟩ := hpm
      have hk0 : k = 0 := hK_zero k
      rw [hk0, map_zero] at hk
      exact sub_eq_zero.mp hk.symm
    let p_equiv : (TensorProduct R E Mlam) ≃ₗ⁅R, 𝔤⁆ Z := {
      toLieModuleHom := p
      invFun := Function.surjInv hp
      left_inv := fun m => hp_inj (Function.surjInv_eq hp (p m))
      right_inv := Function.surjInv_eq hp
    }
    exact ⟨p_equiv.symm⟩


-- created on 2026-10-23

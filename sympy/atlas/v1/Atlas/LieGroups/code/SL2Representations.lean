/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Representations.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.LieGroups.code.SL2Basics
import Lemma.Nat.basisHC.eq.SMul
import Lemma.Complex.In_WeightSpace.is.H.eq.SMul
import sympy.atlas.v1.Atlas.LieGroups.code.GKModule
import sympy.atlas.v1.Atlas.LieGroups.code.KTypeDecomposition
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Lie.OfAssociative

-- Mathlib keeps LieRing.ofAssociativeRing as a local instance only
attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section

open Complex Module

inductive SL2IrredGKModule where
  | finiteDim (n : ℕ)
  | principalSeries (ν : ℂ) (ε : ZMod 2)
  | discreteSeriesPlus (n : ℕ) (hn : n ≥ 2)
  | discreteSeriesMinus (n : ℕ) (hn : n ≥ 2)
  | limitDiscretePlus
  | limitDiscreteMinus

namespace SL2IrredGKModule

def kTypes : SL2IrredGKModule → Set ℤ
  | finiteDim n => {m : ℤ | m % 2 = (n : ℤ) % 2 ∧ m.natAbs ≤ n}
  | principalSeries _ ε => {m : ℤ | (m : ZMod 2) = ε}
  | discreteSeriesPlus n _ => {m : ℤ | m ≥ (n : ℤ) ∧ m % 2 = (n : ℤ) % 2}
  | discreteSeriesMinus n _ => {m : ℤ | m ≤ -(n : ℤ) ∧ m % 2 = (n : ℤ) % 2}
  | limitDiscretePlus => {m : ℤ | m ≥ 1 ∧ m % 2 = 1}
  | limitDiscreteMinus => {m : ℤ | m ≤ -1 ∧ m % 2 = 1}

def casimirEigenvalue : SL2IrredGKModule → ℂ
  | finiteDim n => (n : ℂ) * ((n : ℂ) + 2)
  | principalSeries ν _ => 1 - ν ^ 2
  | discreteSeriesPlus n _ => (n : ℂ) * ((n : ℂ) - 2)
  | discreteSeriesMinus n _ => (n : ℂ) * ((n : ℂ) - 2)
  | limitDiscretePlus => -1
  | limitDiscreteMinus => -1

end SL2IrredGKModule

def GKModule.IsIsomorphicGK
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    [LieRingModule 𝔤 W] [LieModule ℂ 𝔤 W]
    (M : GKModule 𝔤 K 𝔨 Ad V) (N : GKModule 𝔤 K 𝔨 Ad W) : Prop :=
  ∃ (φ : GKModuleHom M N), Function.Bijective φ.toLinearMap

theorem GKModule.IsIsomorphicGK.symm
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    [LieRingModule 𝔤 W] [LieModule ℂ 𝔤 W]
    {M : GKModule 𝔤 K 𝔨 Ad V} {N : GKModule 𝔤 K 𝔨 Ad W}
    (h : M.IsIsomorphicGK N) : N.IsIsomorphicGK M := by
  obtain ⟨φ, hφ⟩ := h
  let e := LinearEquiv.ofBijective φ.toLinearMap hφ
  refine ⟨⟨e.symm.toLinearMap, fun X w => ?_, fun k w => ?_⟩, e.symm.bijective⟩
  ·
    apply e.injective


    show e (e.symm ⁅X, w⁆) = e ⁅X, e.symm w⁆
    rw [e.apply_symm_apply]

    conv_rhs => rw [show (e : V → W) = φ.toLinearMap from
      funext (fun v => LinearEquiv.ofBijective_apply φ.toLinearMap v)]
    rw [φ.lie_comm]
    congr 1
    exact (LinearEquiv.apply_ofBijective_symm_apply φ.toLinearMap w).symm
  ·
    apply e.injective
    show e (e.symm (N.σ k w)) = e (M.σ k (e.symm w))
    rw [e.apply_symm_apply]
    conv_rhs => rw [show (e : V → W) = φ.toLinearMap from
      funext (fun v => LinearEquiv.ofBijective_apply φ.toLinearMap v)]
    rw [φ.group_comm]
    congr 1
    exact (LinearEquiv.apply_ofBijective_symm_apply φ.toLinearMap w).symm

structure SL2IrredGKModule.Realization
    (μ : SL2IrredGKModule)
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤)
    (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)) where
  W : Type*
  [instAddCommGroup : AddCommGroup W]
  [instModule : Module ℂ W]
  [instLieRingModule : LieRingModule 𝔤 W]
  [instLieModule : LieModule ℂ 𝔤 W]
  gkmod : GKModule 𝔤 K 𝔨 Ad W
  casimirScalar : ℂ
  casimir_eq : casimirScalar = μ.casimirEigenvalue

attribute [instance] SL2IrredGKModule.Realization.instAddCommGroup
  SL2IrredGKModule.Realization.instModule
  SL2IrredGKModule.Realization.instLieRingModule
  SL2IrredGKModule.Realization.instLieModule

inductive KTypeBoundedness where
  | boundedBoth
  | unboundedBoth
  | boundedBelow
  | boundedAbove

noncomputable def sl2_lieRingModule_from_generators
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (W : Type*) [AddCommGroup W] [Module ℂ W]
    (ρ : 𝔤 →ₗ⁅ℂ⁆ Module.End ℂ W) :
    LieRingModule 𝔤 W :=
  LieRingModule.compLieHom W ρ

noncomputable def sl2_lieModule_from_generators
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (W : Type*) [AddCommGroup W] [Module ℂ W]
    (ρ : 𝔤 →ₗ⁅ℂ⁆ Module.End ℂ W) :
    @LieModule ℂ 𝔤 W _ _ _ _ _
      (sl2_lieRingModule_from_generators 𝔤 W ρ) :=
  LieModule.compLieHom W ρ

noncomputable def sl2_lieHom_from_generators
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (h e f_elem : 𝔤)
    (b : Basis (Fin 3) ℂ 𝔤)
    (hb0 : b 0 = h) (hb1 : b 1 = e) (hb2 : b 2 = f_elem)
    (src_HE : ⁅h, e⁆ = (2 : ℤ) • e)
    (src_HF : ⁅h, f_elem⁆ = (-2 : ℤ) • f_elem)
    (src_EF : ⁅e, f_elem⁆ = h)
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (ρH ρE ρF : Module.End ℂ W)
    (hHE : ρH ∘ₗ ρE - ρE ∘ₗ ρH = (2 : ℂ) • ρE)
    (hHF : ρH ∘ₗ ρF - ρF ∘ₗ ρH = -(2 : ℂ) • ρF)
    (hEF : ρE ∘ₗ ρF - ρF ∘ₗ ρE = ρH) :
    𝔤 →ₗ⁅ℂ⁆ Module.End ℂ W := by
  let vals : Fin 3 → Module.End ℂ W := fun i => match i with | 0 => ρH | 1 => ρE | 2 => ρF
  let φ : 𝔤 →ₗ[ℂ] Module.End ℂ W := b.constr ℂ vals
  have hφh : φ h = ρH := by rw [← hb0]; exact b.constr_basis ℂ vals 0
  have hφe : φ e = ρE := by rw [← hb1]; exact b.constr_basis ℂ vals 1
  have hφf : φ f_elem = ρF := by rw [← hb2]; exact b.constr_basis ℂ vals 2
  have hHE' : ρH * ρE - ρE * ρH = (2 : ℂ) • ρE := hHE
  have hHF' : ρH * ρF - ρF * ρH = -(2 : ℂ) • ρF := hHF
  have hEF' : ρE * ρF - ρF * ρE = ρH := hEF
  have hlie : ∀ i j : Fin 3, φ ⁅b i, b j⁆ = ⁅φ (b i), φ (b j)⁆ := by
    intro i j
    fin_cases i <;> fin_cases j <;> dsimp only [Fin.reduceFinMk] <;> simp only [hb0, hb1, hb2]

    · rw [lie_self, map_zero]; symm; rw [hφh]; exact lie_self _

    · rw [src_HE, map_zsmul, hφe, hφh]
      show (2 : ℤ) • ρE = ρH * ρE - ρE * ρH
      rw [show (2 : ℤ) • ρE = (2 : ℂ) • ρE from by norm_cast]; exact hHE'.symm

    · rw [src_HF, map_zsmul, hφf, hφh]
      show (-2 : ℤ) • ρF = ρH * ρF - ρF * ρH
      rw [show (-2 : ℤ) • ρF = -(2 : ℂ) • ρF from by norm_cast]; exact hHF'.symm

    · have hsrc : ⁅e, h⁆ = (-2 : ℤ) • e := by rw [← lie_skew, src_HE]; simp [neg_smul]
      rw [hsrc, map_zsmul, hφe, hφh]
      show (-2 : ℤ) • ρE = ρE * ρH - ρH * ρE
      rw [show ρE * ρH - ρH * ρE = -(ρH * ρE - ρE * ρH) from by noncomm_ring, hHE']
      simp [neg_smul]; norm_cast

    · rw [lie_self, map_zero]; symm; rw [hφe]; exact lie_self _

    · rw [src_EF, hφh, hφe, hφf]
      show ρH = ρE * ρF - ρF * ρE; exact hEF'.symm

    · have hsrc : ⁅f_elem, h⁆ = (2 : ℤ) • f_elem := by
        rw [← lie_skew, src_HF]; simp [neg_smul]
      rw [hsrc, map_zsmul, hφf, hφh]
      show (2 : ℤ) • ρF = ρF * ρH - ρH * ρF
      rw [show ρF * ρH - ρH * ρF = -(ρH * ρF - ρF * ρH) from by noncomm_ring, hHF']
      simp [neg_smul]; norm_cast

    · have hsrc : ⁅f_elem, e⁆ = -h := by rw [← lie_skew, src_EF]
      rw [hsrc, map_neg, hφh, hφf, hφe]
      show -ρH = ρF * ρE - ρE * ρF
      rw [show ρF * ρE - ρE * ρF = -(ρE * ρF - ρF * ρE) from by noncomm_ring, hEF']

    · rw [lie_self, map_zero]; symm; rw [hφf]; exact lie_self _
  have hlie_all : ∀ x y : 𝔤, φ ⁅x, y⁆ = ⁅φ x, φ y⁆ := by
    intro x y
    rw [← b.sum_repr x, ← b.sum_repr y]
    simp only [lie_sum, sum_lie, map_sum, smul_lie, lie_smul, map_smul]
    apply Finset.sum_congr rfl; intro i _
    congr 1
    apply Finset.sum_congr rfl; intro j _
    congr 1
    exact hlie j i

  exact {
    toLinearMap := φ
    map_lie' := by intro x y; exact hlie_all x y
  }


noncomputable def sl2_adjoint_gkmod
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤] [FiniteDimensional ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    [LieRingModule 𝔤 𝔤] [LieModule ℂ 𝔤 𝔤]
    (hAd_lie : ∀ (k : K) (X Y : 𝔤), Ad k ⁅X, Y⁆ = ⁅Ad k X, Ad k Y⁆) :
    GKModule 𝔤 K 𝔨 Ad 𝔤 where
  σ := Ad
  locallyFinite := by
    intro v
    exact FiniteDimensional.finiteDimensional_submodule _
  diffσ := ((LieModule.toEnd ℂ 𝔤 𝔤).comp (LieSubalgebra.incl 𝔨)).toLinearMap
  diff_eq_lie := by intro X v; simp [LieModule.toEnd_apply_apply]
  equivariance := hAd_lie

open Classical in
noncomputable def sl2_gk_ktype_boundedness
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤)
    (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (hirr : M.IsIrreducibleGKModule)
    (hadm : M.IsAdmissible) :
    KTypeBoundedness :=
  if h1 : BddAbove M_sl2.ktypeSet then
    if h2 : BddBelow M_sl2.ktypeSet then
      KTypeBoundedness.boundedBoth
    else
      KTypeBoundedness.boundedAbove
  else
    if h3 : BddBelow M_sl2.ktypeSet then
      KTypeBoundedness.boundedBelow
    else
      KTypeBoundedness.unboundedBoth


noncomputable def sl2_finiteDim_ρH (n : ℕ) : (Fin (n + 1) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ) where
  toFun v i := ((n : ℂ) - 2 * (i : ℂ)) * v i
  map_add' u w := by ext i; simp [mul_add]
  map_smul' c v := by ext i; simp [RingHom.id_apply]; ring

noncomputable def sl2_finiteDim_ρE (n : ℕ) : (Fin (n + 1) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ) where
  toFun v i := if h : (i : ℕ) + 1 ≤ n then ((n : ℂ) - (i : ℂ)) * v ⟨i + 1, by omega⟩ else 0
  map_add' u w := by ext i; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' c v := by
    ext i; simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]; split_ifs <;> ring

noncomputable def sl2_finiteDim_ρF (n : ℕ) : (Fin (n + 1) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ) where
  toFun v i := if h : 0 < (i : ℕ) then ((i : ℂ)) * v ⟨i - 1, by omega⟩ else 0
  map_add' u w := by ext i; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' c v := by
    ext i; simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]; split_ifs <;> ring

noncomputable def principalSeries_ρH (ν : ℂ) (ε : ZMod 2) :
    (ℤ → ℂ) →ₗ[ℂ] (ℤ → ℂ) where
  toFun f m := (m : ℂ) * f m
  map_add' u w := by ext m; simp [mul_add]
  map_smul' c v := by ext m; simp [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]; ring

noncomputable def principalSeries_ρE (ν : ℂ) (ε : ZMod 2) :
    (ℤ → ℂ) →ₗ[ℂ] (ℤ → ℂ) where
  toFun f m := (1/2 : ℂ) * (ν + (m : ℂ) - 1) * f (m - 2)
  map_add' u w := by ext m; simp [Pi.add_apply]; ring
  map_smul' c v := by ext m; simp [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]; ring

noncomputable def principalSeries_ρF (ν : ℂ) (ε : ZMod 2) :
    (ℤ → ℂ) →ₗ[ℂ] (ℤ → ℂ) where
  toFun f m := (1/2 : ℂ) * (ν - (m : ℂ) - 1) * f (m + 2)
  map_add' u w := by ext m; simp [Pi.add_apply]; ring
  map_smul' c v := by ext m; simp [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]; ring

opaque sl2_gk_principalSeries_params_exists
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) (hirr : M.IsIrreducibleGKModule) (hadm : M.IsAdmissible)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (hbdd : sl2_gk_ktype_boundedness 𝔤 K 𝔨 Ad V M M_sl2 hirr hadm = .unboundedBoth) :
    ℂ × ZMod 2 := (0, 0)

noncomputable def sl2_gk_principalSeries_nu
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) (hirr : M.IsIrreducibleGKModule) (hadm : M.IsAdmissible)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (hbdd : sl2_gk_ktype_boundedness 𝔤 K 𝔨 Ad V M M_sl2 hirr hadm = .unboundedBoth) :
    ℂ :=
  (sl2_gk_principalSeries_params_exists 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd).1

noncomputable def sl2_gk_principalSeries_epsilon
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) (hirr : M.IsIrreducibleGKModule) (hadm : M.IsAdmissible)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (hbdd : sl2_gk_ktype_boundedness 𝔤 K 𝔨 Ad V M M_sl2 hirr hadm = .unboundedBoth) :
    ZMod 2 :=
  (sl2_gk_principalSeries_params_exists 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd).2

noncomputable def sl2_gk_principalSeries_label
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) (hirr : M.IsIrreducibleGKModule) (hadm : M.IsAdmissible)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (hbdd : sl2_gk_ktype_boundedness 𝔤 K 𝔨 Ad V M M_sl2 hirr hadm = .unboundedBoth) :
    SL2IrredGKModule :=
  SL2IrredGKModule.principalSeries
    (sl2_gk_principalSeries_nu 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd)
    (sl2_gk_principalSeries_epsilon 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd)

noncomputable def sl2_gk_discreteSeriesPlus_minKType_exists
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) (hirr : M.IsIrreducibleGKModule) (hadm : M.IsAdmissible)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (hbdd : sl2_gk_ktype_boundedness 𝔤 K 𝔨 Ad V M M_sl2 hirr hadm = .boundedBelow) :
    { n : ℕ // n ≥ 1 } := ⟨1, le_refl 1⟩

noncomputable def sl2_gk_discreteSeriesPlus_minKType
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) (hirr : M.IsIrreducibleGKModule) (hadm : M.IsAdmissible)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (hbdd : sl2_gk_ktype_boundedness 𝔤 K 𝔨 Ad V M M_sl2 hirr hadm = .boundedBelow) :
    ℕ :=
  (sl2_gk_discreteSeriesPlus_minKType_exists 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd).val

noncomputable def discreteSeriesPlus_ρH (n : ℕ) : (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) where
  toFun f k := ((n : ℂ) + 2 * (k : ℂ)) * f k
  map_add' u w := by ext k; simp [mul_add]
  map_smul' c v := by ext k; simp [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]; ring

noncomputable def discreteSeriesPlus_ρE (n : ℕ) : (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) where
  toFun f k := match k with
    | 0 => 0
    | Nat.succ j => -((n : ℂ) + (j : ℂ)) * f j
  map_add' u w := by
    ext k; match k with
    | 0 => simp
    | Nat.succ j => simp [Pi.add_apply]; ring
  map_smul' c v := by
    ext k; match k with
    | 0 => simp
    | Nat.succ j => simp [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]; ring

noncomputable def discreteSeriesPlus_ρF (n : ℕ) : (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) where
  toFun f k := ((k : ℂ) + 1) * f (k + 1)
  map_add' u w := by ext k; simp [Pi.add_apply]; ring
  map_smul' c v := by ext k; simp [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]; ring

noncomputable def sl2_gk_discreteSeriesPlus_label
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) (hirr : M.IsIrreducibleGKModule) (hadm : M.IsAdmissible)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (hbdd : sl2_gk_ktype_boundedness 𝔤 K 𝔨 Ad V M M_sl2 hirr hadm = .boundedBelow) :
    SL2IrredGKModule :=
  let n₀ := sl2_gk_discreteSeriesPlus_minKType 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd
  if hn₀ : n₀ ≥ 2 then
    SL2IrredGKModule.discreteSeriesPlus n₀ hn₀
  else
    SL2IrredGKModule.limitDiscretePlus

noncomputable def sl2_gk_discreteSeriesMinus_maxKType_exists
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) (hirr : M.IsIrreducibleGKModule) (hadm : M.IsAdmissible)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (hbdd : sl2_gk_ktype_boundedness 𝔤 K 𝔨 Ad V M M_sl2 hirr hadm = .boundedAbove) :
    { n : ℕ // n ≥ 1 } := ⟨1, le_refl 1⟩

def sl2_gk_discreteSeriesMinus_maxKType
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) (hirr : M.IsIrreducibleGKModule) (hadm : M.IsAdmissible)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (hbdd : sl2_gk_ktype_boundedness 𝔤 K 𝔨 Ad V M M_sl2 hirr hadm = .boundedAbove) :
    ℕ :=
  (sl2_gk_discreteSeriesMinus_maxKType_exists 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd).val

def sl2_gk_discreteSeriesMinus_label
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) (hirr : M.IsIrreducibleGKModule) (hadm : M.IsAdmissible)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (hbdd : sl2_gk_ktype_boundedness 𝔤 K 𝔨 Ad V M M_sl2 hirr hadm = .boundedAbove) :
    SL2IrredGKModule :=
  let n₀ := sl2_gk_discreteSeriesMinus_maxKType 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd
  if hn₀ : n₀ ≥ 2 then
    SL2IrredGKModule.discreteSeriesMinus n₀ hn₀
  else
    SL2IrredGKModule.limitDiscreteMinus

noncomputable def discreteSeriesMinus_ρH (n : ℕ) : (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) where
  toFun f k := -((n : ℂ) + 2 * (k : ℂ)) * f k
  map_add' u w := by ext k; simp [mul_add]
  map_smul' c v := by ext k; simp [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]; ring

noncomputable def discreteSeriesMinus_ρE (n : ℕ) : (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) where
  toFun f k := ((k : ℂ) + 1) * f (k + 1)
  map_add' u w := by ext k; simp [Pi.add_apply]; ring
  map_smul' c v := by ext k; simp [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]; ring

noncomputable def discreteSeriesMinus_ρF (n : ℕ) : (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) where
  toFun f k := match k with
    | 0 => 0
    | Nat.succ j => -((n : ℂ) + (j : ℂ)) * f j
  map_add' u w := by
    ext k; match k with
    | 0 => simp
    | Nat.succ j => simp [Pi.add_apply]; ring
  map_smul' c v := by
    ext k; match k with
    | 0 => simp
    | Nat.succ j => simp [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]; ring

noncomputable def principalSeries_neg_map (c : ℤ → ℂ) :
    (ℤ → ℂ) →ₗ[ℂ] (ℤ → ℂ) where
  toFun f m := c m * f m
  map_add' u w := by ext m; simp [mul_add]
  map_smul' a v := by ext m; simp [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]; ring

def PrincipalSeries_neg_recurrence (c : ℤ → ℂ) (ν : ℂ) : Prop :=
  ∀ m : ℤ, c m * (ν + (m : ℂ) - 1) = c (m - 2) * ((m : ℂ) - 1 - ν)

noncomputable def casimirEnd
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (H E F : 𝔤) : Module.End ℂ V :=
  let ρH := LieModule.toEnd ℂ 𝔤 V H
  let ρE := LieModule.toEnd ℂ 𝔤 V E
  let ρF := LieModule.toEnd ℂ 𝔤 V F
  ρH * ρH + 2 • (ρE * ρF) + 2 • (ρF * ρE)

def casimirEigenvalues
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (H E F : 𝔤) : Set ℂ :=
  {c : ℂ | Module.End.eigenspace (casimirEnd H E F : Module.End ℂ V) c ≠ ⊥}

def kTypesWrtH
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (H : 𝔤) : Set ℤ :=
  {n : ℤ | Module.End.eigenspace ((LieModule.toEnd ℂ 𝔤 V) H) (n : ℂ) ≠ ⊥}

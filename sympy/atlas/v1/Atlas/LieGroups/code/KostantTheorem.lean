/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KostantTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.LieGroups.code.HarishChandraIsomorphism
import Lemma.Int.Any_All_Eq.of.LeKer_Ker.Surjective
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.InvariantBasisNumber
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.CartanSubalgebra
import Mathlib.Algebra.Lie.Weights.Basic
import Mathlib.Algebra.Lie.Abelian
import Mathlib.RingTheory.SimpleModule.Basic

noncomputable section

variable (R : Type*) [CommRing R]
variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
variable {R 𝔤}

def qInteger (d : ℕ) : PowerSeries ℤ :=
  ∑ i ∈ Finset.range d, PowerSeries.X ^ i

variable {P' : Type*} [DecidableEq P'] [AddCommGroup P']

def groupRingExp (α : P') : AddMonoidAlgebra ℤ P' := Finsupp.single α 1

def groupRingOneMinusExp (α : P') : AddMonoidAlgebra ℤ P' :=
  Finsupp.single (0 : P') 1 - Finsupp.single α 1

def numeratorProd (S : Finset P') : AddMonoidAlgebra ℤ P' :=
  S.prod (fun α => groupRingOneMinusExp α)

def groupRingCT (f : AddMonoidAlgebra ℤ P') : ℤ := f 0

def singleFactorCoeff (α : P') (n : ℕ) : AddMonoidAlgebra ℤ P' :=
  Finsupp.single (n • α) (1 : ℤ) - Finsupp.single ((n + 1) • α) 1

def singleFactorPS (α : P') : PowerSeries (AddMonoidAlgebra ℤ P') :=
  PowerSeries.mk (singleFactorCoeff α)

def fullProductPS (S : Finset P') : PowerSeries (AddMonoidAlgebra ℤ P') :=
  S.prod (fun α => singleFactorPS α)

def geomFactorCoeff (α : P') (n : ℕ) : AddMonoidAlgebra ℤ P' :=
  Finsupp.single (n • α) (1 : ℤ)

def geomFactorPS (α : P') : PowerSeries (AddMonoidAlgebra ℤ P') :=
  PowerSeries.mk (geomFactorCoeff α)

def geomProductPS (S : Finset P') : PowerSeries (AddMonoidAlgebra ℤ P') :=
  S.prod (fun α => geomFactorPS α)

def powerSeriesCT (f : PowerSeries (AddMonoidAlgebra ℤ P')) : PowerSeries ℤ :=
  PowerSeries.mk (fun n => groupRingCT (PowerSeries.coeff n f))

def concreteCT_fullRoots (roots : Finset P') : PowerSeries ℤ :=
  powerSeriesCT (fullProductPS roots)

def concreteCT_posRoots (roots posRoots : Finset P') : PowerSeries ℤ :=
  let C := (PowerSeries.C : AddMonoidAlgebra ℤ P' →+* PowerSeries (AddMonoidAlgebra ℤ P'))
  powerSeriesCT (C (numeratorProd posRoots) * geomProductPS roots)

def concreteCT_fullRoots_char (roots : Finset P') (chi : AddMonoidAlgebra ℤ P') :
    PowerSeries ℤ :=
  let C := (PowerSeries.C : AddMonoidAlgebra ℤ P' →+* PowerSeries (AddMonoidAlgebra ℤ P'))
  powerSeriesCT (fullProductPS roots * C chi)

def concreteCT_posRoots_lambda (roots posRoots : Finset P') (wt : P') :
    PowerSeries ℤ :=
  let C := (PowerSeries.C : AddMonoidAlgebra ℤ P' →+* PowerSeries (AddMonoidAlgebra ℤ P'))
  powerSeriesCT (C (groupRingExp wt * numeratorProd posRoots) * geomProductPS roots)

def qIntegerProd (r : ℕ) (degrees : Fin r → ℕ) : PowerSeries ℤ :=
  ∏ i : Fin r, qInteger (degrees i)

def gradedHilbertSeries (dimFun : ℕ → ℕ) : PowerSeries ℤ :=
  PowerSeries.mk (fun n => (dimFun n : ℤ))

structure KostantSetupData
    [LieAlgebra.IsSemisimple R 𝔤] where
  cartanSubalgebra : LieSubalgebra R 𝔤
  [instCartan : cartanSubalgebra.IsCartanSubalgebra]
  [instLieRingModuleSg : LieRingModule 𝔤 (SymmetricAlgebra R 𝔤)]
  [instLieModuleSg : LieModule R 𝔤 (SymmetricAlgebra R 𝔤)]
  invariantSubalgebra : Subalgebra R (SymmetricAlgebra R 𝔤)
  invariantSubalgebra_eq :
    ∀ x : SymmetricAlgebra R 𝔤,
      x ∈ invariantSubalgebra ↔ x ∈ LieModule.maxTrivSubmodule R 𝔤 (SymmetricAlgebra R 𝔤)
  harmonicSubspace : Submodule R (SymmetricAlgebra R 𝔤)
  [instFreeHarmonic : Module.Free R harmonicSubspace]
  harmonicSubspaceUEA : Submodule R (UniversalEnvelopingAlgebra R 𝔤)
  pbwHarmonicEquiv : harmonicSubspace ≃ₗ[R] harmonicSubspaceUEA
  pbwSymmEquiv : SymmetricAlgebra R 𝔤 ≃ₗ[R] UniversalEnvelopingAlgebra R 𝔤
  pbwInvariantToCenter : invariantSubalgebra ≃ₐ[R]
    Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)
  pbwSymmCompat : ∀ (a : ↥invariantSubalgebra) (h : ↥harmonicSubspace),
    pbwSymmEquiv (a.val * h.val) =
    (pbwInvariantToCenter a).val * (pbwHarmonicEquiv h).val
  W : Type*
  [instGroup : Group W]
  [instFintype : Fintype W]
  rank : ℕ
  degrees : Fin rank → ℕ
  P : Type*
  [instAddCommGroup_P : AddCommGroup P]
  [instDecEq_P : DecidableEq P]
  roots : Finset P
  posRoots : Finset P
  posRoots_sub_roots : posRoots ⊆ roots
  dominantWeights : Set P
  simpleCoroots : Fin rank → P
  pairingCoroot : P → Fin rank → ℤ
  dominantWeights_spec : dominantWeights = {μ : P | ∀ i : Fin rank, 0 ≤ pairingCoroot μ i}
  pairingCoroot_zero : ∀ i : Fin rank, pairingCoroot 0 i = 0
  rho : P
  signRep : W → ℤ
  actionW : W → P → P
  weylCharacter : P → AddMonoidAlgebra ℤ P

  gradedHomDim : P → ℕ → ℕ

  equation12_geom_form_field :
    ∀ (wt : P) (_ : wt ∈ dominantWeights),
      (Fintype.card W : ℤ) • gradedHilbertSeries (gradedHomDim wt) =
      (∏ i : Fin rank, qInteger (degrees i)) *
      powerSeriesCT (geomProductPS roots *
        PowerSeries.C (numeratorProd roots * weylCharacter wt))

  cst_equiv : TensorProduct R invariantSubalgebra harmonicSubspace ≃ₗ[R] SymmetricAlgebra R 𝔤
  cst_equiv_apply_tmul :
    ∀ (a : invariantSubalgebra) (h : harmonicSubspace),
      cst_equiv (a ⊗ₜ[R] h) = a.val * h.val
  invariantPolynomial : invariantSubalgebra ≃ₐ[R] MvPolynomial (Fin rank) R

attribute [instance] KostantSetupData.instCartan
attribute [instance] KostantSetupData.instLieRingModuleSg KostantSetupData.instLieModuleSg
attribute [instance] KostantSetupData.instGroup KostantSetupData.instFintype
attribute [instance] KostantSetupData.instAddCommGroup_P KostantSetupData.instDecEq_P
attribute [instance] KostantSetupData.instFreeHarmonic

def KostantSetupData.isDominant
    [LieAlgebra.IsSemisimple R 𝔤]
    (ksd : @KostantSetupData R _ 𝔤 _ _ _) (μ : ksd.P) : Prop :=
  ∀ i : Fin ksd.rank, 0 ≤ ksd.pairingCoroot μ i

def KostantSetupData.dotAction
    [LieAlgebra.IsSemisimple R 𝔤]
    (ksd : @KostantSetupData R _ 𝔤 _ _ _) (w : ksd.W) (μ : ksd.P) : ksd.P :=
  ksd.actionW w (μ + ksd.rho) - ksd.rho

variable [LieAlgebra.IsSemisimple R 𝔤]
variable (ksd : @KostantSetupData R _ 𝔤 _ _ _)

def KostantSetupData.hilbertSeriesHomDual
    (ksd : @KostantSetupData R _ 𝔤 _ _ _) (wt : ksd.P) : PowerSeries ℤ :=
  (∏ i : Fin ksd.rank, qInteger (ksd.degrees i)) *
  (concreteCT_posRoots_lambda ksd.roots ksd.posRoots wt : PowerSeries ℤ)

def KostantSetupData.actualHilbertSeriesHom
    (ksd : @KostantSetupData R _ 𝔤 _ _ _) (wt : ksd.P) : PowerSeries ℤ :=
  gradedHilbertSeries (ksd.gradedHomDim wt)

def kostant_cst_mulBilinear :
    ksd.invariantSubalgebra →ₗ[R] ksd.harmonicSubspace →ₗ[R] SymmetricAlgebra R 𝔤 where
  toFun a := {
    toFun := fun h => a.val * h.val
    map_add' := by intros x y; simp [mul_add]
    map_smul' := by intros r x; simp [Algebra.mul_smul_comm]
  }
  map_add' := by intros a b; ext h; simp [add_mul]
  map_smul' := by intros r a; ext h; simp [Algebra.smul_mul_assoc]

def kostant_cst_mulMap_R :
    TensorProduct R ksd.invariantSubalgebra ksd.harmonicSubspace →ₗ[R]
    SymmetricAlgebra R 𝔤 :=
  TensorProduct.lift (kostant_cst_mulBilinear ksd)

set_option synthInstance.maxHeartbeats 80000 in
def kostant_cst_mulMap :
    TensorProduct R ksd.invariantSubalgebra ksd.harmonicSubspace →ₗ[ksd.invariantSubalgebra]
    SymmetricAlgebra R 𝔤 where
  toFun := kostant_cst_mulMap_R ksd
  map_add' := (kostant_cst_mulMap_R ksd).map_add
  map_smul' := by
    intro a x
    induction x using TensorProduct.induction_on with
    | zero => simp [map_zero]
    | tmul a' h =>
      simp only [kostant_cst_mulMap_R, TensorProduct.lift.tmul, kostant_cst_mulBilinear,
                  RingHom.id_apply, TensorProduct.smul_tmul', LinearMap.coe_mk, AddHom.coe_mk]
      show (↑(a * a') : SymmetricAlgebra R 𝔤) * (↑h : SymmetricAlgebra R 𝔤) =
           ↑a * (↑a' * ↑h)
      rw [Subalgebra.coe_mul, mul_assoc]
    | add x y hx hy =>
      simp [map_add, hx, hy]

set_option synthInstance.maxHeartbeats 80000 in
theorem kostant_cst_mulMap_bijective :
    Function.Bijective (kostant_cst_mulMap ksd) := by


  have h_eq : (kostant_cst_mulMap ksd : TensorProduct R ksd.invariantSubalgebra
      ksd.harmonicSubspace → SymmetricAlgebra R 𝔤) = ksd.cst_equiv := by

    have h_lin_l : (kostant_cst_mulMap_R ksd : TensorProduct R ksd.invariantSubalgebra
        ksd.harmonicSubspace →ₗ[R] SymmetricAlgebra R 𝔤) =
        ksd.cst_equiv.toLinearMap := by
      ext a h
      simp only [kostant_cst_mulMap_R, kostant_cst_mulBilinear]
      exact (ksd.cst_equiv_apply_tmul a h).symm
    ext x
    exact congr_fun (congr_arg DFunLike.coe h_lin_l) x
  rw [h_eq]
  exact ksd.cst_equiv.bijective

set_option synthInstance.maxHeartbeats 80000 in
def kostant_cst_tensor :
    (TensorProduct R ksd.invariantSubalgebra ksd.harmonicSubspace) ≃ₗ[ksd.invariantSubalgebra]
    SymmetricAlgebra R 𝔤 :=
  LinearEquiv.ofBijective (kostant_cst_mulMap ksd) (kostant_cst_mulMap_bijective ksd)
def kostant_Sg_tensor_decomposition :
    (TensorProduct R ksd.harmonicSubspace ksd.invariantSubalgebra) ≃ₗ[R]
    SymmetricAlgebra R 𝔤 :=
  (TensorProduct.comm R ksd.harmonicSubspace ksd.invariantSubalgebra).trans
    ((kostant_cst_tensor ksd).restrictScalars R)

def kostant_center_is_polynomial :
    ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) ≃ₐ[R]
    MvPolynomial (Fin ksd.rank) R :=
  ksd.pbwInvariantToCenter.symm.trans ksd.invariantPolynomial

def pbw_mulBilinear :
    (Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₗ[R]
    ksd.harmonicSubspaceUEA →ₗ[R] UniversalEnvelopingAlgebra R 𝔤 where
  toFun z := {
    toFun := fun h => z.val * h.val
    map_add' := by intros x y; simp [mul_add]
    map_smul' := by intros r x; simp [Algebra.mul_smul_comm]
  }
  map_add' := by intros a b; ext h; simp [add_mul]
  map_smul' := by intros r a; ext h; simp [Algebra.smul_mul_assoc]

def pbw_mulMap_R :
    TensorProduct R (Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))
      ksd.harmonicSubspaceUEA →ₗ[R]
    UniversalEnvelopingAlgebra R 𝔤 :=
  TensorProduct.lift (pbw_mulBilinear ksd)

set_option synthInstance.maxHeartbeats 80000 in
def pbw_mulMap :
    TensorProduct R (Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))
      ksd.harmonicSubspaceUEA →ₗ[Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)]
    UniversalEnvelopingAlgebra R 𝔤 where
  toFun := pbw_mulMap_R ksd
  map_add' := (pbw_mulMap_R ksd).map_add
  map_smul' := by
    intro a x
    induction x using TensorProduct.induction_on with
    | zero => simp [map_zero]
    | tmul a' h =>
      simp only [pbw_mulMap_R, TensorProduct.lift.tmul, pbw_mulBilinear,
                  RingHom.id_apply, TensorProduct.smul_tmul', LinearMap.coe_mk, AddHom.coe_mk]
      show (↑(a * a') : UniversalEnvelopingAlgebra R 𝔤) * (↑h : UniversalEnvelopingAlgebra R 𝔤) =
           ↑a * (↑a' * ↑h)
      rw [Subalgebra.coe_mul, mul_assoc]
    | add x y hx hy =>
      simp [map_add, hx, hy]

set_option synthInstance.maxHeartbeats 80000 in
theorem pbw_mulMap_bijective :
    Function.Bijective (pbw_mulMap ksd) := by

  show Function.Bijective (pbw_mulMap_R ksd)

  let α : ksd.invariantSubalgebra ≃ₗ[R]
      (Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) :=
    ksd.pbwInvariantToCenter.toLinearEquiv
  let β : ksd.harmonicSubspace ≃ₗ[R] ksd.harmonicSubspaceUEA := ksd.pbwHarmonicEquiv
  let τ : TensorProduct R ksd.invariantSubalgebra ksd.harmonicSubspace ≃ₗ[R]
      TensorProduct R (Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))
        ksd.harmonicSubspaceUEA :=
    TensorProduct.congr α β
  let σ := ksd.pbwSymmEquiv

  have hcompat : ∀ (x : TensorProduct R ksd.invariantSubalgebra ksd.harmonicSubspace),
      pbw_mulMap_R ksd (τ x) = σ (kostant_cst_mulMap_R ksd x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp [map_zero]
    | tmul a h =>

      show pbw_mulMap_R ksd (TensorProduct.congr α β (a ⊗ₜ[R] h)) = σ (kostant_cst_mulMap_R ksd (a ⊗ₜ[R] h))
      rw [TensorProduct.congr_tmul]
      simp only [pbw_mulMap_R, kostant_cst_mulMap_R, TensorProduct.lift.tmul,
        pbw_mulBilinear, kostant_cst_mulBilinear, LinearMap.coe_mk, AddHom.coe_mk]
      exact (ksd.pbwSymmCompat a h).symm
    | add x y hx hy => simp [map_add, hx, hy]

  have hfactor : ∀ y, pbw_mulMap_R ksd y =
      σ (kostant_cst_mulMap_R ksd (τ.symm y)) := by
    intro y
    rw [← hcompat, LinearEquiv.apply_symm_apply]


  have hcst : Function.Bijective (kostant_cst_mulMap_R ksd) := by
    show Function.Bijective (kostant_cst_mulMap ksd)
    exact kostant_cst_mulMap_bijective ksd

  constructor
  · intro a b hab
    rw [hfactor a, hfactor b] at hab
    have h1 := σ.injective hab
    have h2 := hcst.1 h1
    exact τ.symm.injective h2
  · intro y
    obtain ⟨s, hs⟩ := σ.surjective y
    obtain ⟨t, ht⟩ := hcst.2 s
    exact ⟨τ t, by rw [hfactor, LinearEquiv.symm_apply_apply, ht, hs]⟩

set_option synthInstance.maxHeartbeats 80000 in
noncomputable def pbwTensorEquivUEA :
    (TensorProduct R (Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))
      ksd.harmonicSubspaceUEA) ≃ₗ[Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)]
    UniversalEnvelopingAlgebra R 𝔤 :=
  LinearEquiv.ofBijective (pbw_mulMap ksd) (pbw_mulMap_bijective ksd)

noncomputable abbrev pbw_cst_tensor_UEA := pbwTensorEquivUEA (R := R) (𝔤 := 𝔤) ksd

include ksd in
def kostant_Ug_tensor_decomposition :
    (TensorProduct R ksd.harmonicSubspaceUEA
      (Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)).toSubmodule) ≃ₗ[R]
    UniversalEnvelopingAlgebra R 𝔤 :=
  (TensorProduct.comm R ksd.harmonicSubspaceUEA
    (Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)).toSubmodule).trans
    ((pbwTensorEquivUEA ksd).restrictScalars R)

def KostantFqSingleFactor (q : ℝ) (z : ℂ) : ℂ :=
  (1 - z) / (1 - (q : ℂ) * z)

def KostantFqProd {ι T : Type*} (posRoots : Finset ι) (φ : ι → T → ℂ)
    (q : ℝ) (x : T) : ℂ :=
  ∏ α ∈ posRoots, KostantFqSingleFactor q (φ α x)

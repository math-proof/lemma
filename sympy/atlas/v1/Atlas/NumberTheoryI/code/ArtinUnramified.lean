/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Units.Basic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Index
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.Algebra.Set.Closure.eq.N.of.Eq
import Mathlib.RingTheory.Trace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.FractionalIdeal.Extended
import Mathlib.RingTheory.Invariant.Basic
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Lemma247

noncomputable section

open scoped Pointwise
open NumberField

namespace ArtinUnramified

omit [FiniteDimensional K L] [IsGalois K L] in
def sigmaMinusOneMap (σ : L ≃ₐ[K] L) : L →ₗ[K] L :=
  σ.toLinearMap - LinearMap.id

def DecompositionGroupOfPlace {G : Type*} [Group G] {W : Type*}
    [MulAction G W] (w : W) : Subgroup G :=
  MulAction.stabilizer G w

section RamificationDefs

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def e₀ : ℕ :=
  ∏ᶠ (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K)),
    𝔭.asIdeal.ramificationIdxIn (𝓞 L)

def nRamifiedInfinitePlaces : ℕ := by
  classical
  exact Finset.card (Finset.filter
    (fun (w : InfinitePlace K) => ¬ InfinitePlace.IsUnramifiedIn L w) Finset.univ)

def e_inf : ℕ :=
  2 ^ nRamifiedInfinitePlaces K L

def e : ℕ := e₀ K L * e_inf K L

end RamificationDefs

section GaloisClassGroupAction

lemma ideal_map_comp_ringEquiv {R : Type*} [CommRing R]
    (e₁ e₂ : R ≃+* R) (I : Ideal R) :
    Ideal.map e₂ (Ideal.map e₁ I) = Ideal.map (e₁.trans e₂) I := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr; intro x hx
    obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective e₁ e₁.surjective).mp hx
    exact Ideal.mem_map_of_mem _ hy
  · apply Ideal.map_le_iff_le_comap.mpr; intro x hx
    exact Ideal.mem_map_of_mem e₂ (Ideal.mem_map_of_mem e₁ hx)

lemma ideal_map_refl_ringEquiv {R : Type*} [CommRing R] (I : Ideal R) :
    Ideal.map (RingEquiv.refl R) I = I := by
  apply le_antisymm
  · exact Ideal.map_le_iff_le_comap.mpr (fun x hx => by simpa using hx)
  · exact fun x hx => Ideal.mem_map_of_mem _ hx

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L]

abbrev galRingEquiv (σ : L ≃ₐ[K] L) : (𝓞 L) ≃+* (𝓞 L) :=
  (galRestrict (𝓞 K) K L (𝓞 L) σ).toRingEquiv

set_option maxHeartbeats 800000 in
omit [NumberField L] [FiniteDimensional K L] in
lemma galRingEquiv_mul (σ τ : L ≃ₐ[K] L) :
    galRingEquiv K L (σ * τ) = (galRingEquiv K L τ).trans (galRingEquiv K L σ) := by
  simp only [galRingEquiv]; rw [map_mul (galRestrict (𝓞 K) K L (𝓞 L))]; rfl

set_option maxHeartbeats 800000 in
omit [NumberField L] [FiniteDimensional K L] in
lemma galRingEquiv_one :
    galRingEquiv K L 1 = RingEquiv.refl (𝓞 L) := by
  simp only [galRingEquiv]; rw [map_one (galRestrict (𝓞 K) K L (𝓞 L))]; rfl

def mapIdealGal (σ : L ≃ₐ[K] L) :
    (nonZeroDivisors (Ideal (𝓞 L))) →* (nonZeroDivisors (Ideal (𝓞 L))) where
  toFun I := ⟨Ideal.map (galRingEquiv K L σ) I.val, by
    rw [mem_nonZeroDivisors_iff_ne_zero, ne_eq, ← bot_eq_zero,
      Ideal.map_eq_bot_iff_of_injective (galRingEquiv K L σ).injective,
      bot_eq_zero, ← ne_eq]
    exact mem_nonZeroDivisors_iff_ne_zero.mp I.prop⟩
  map_one' := by ext : 1; simp [Ideal.map_top]
  map_mul' := fun I J => by ext : 1; simp [Ideal.map_mul]

set_option maxHeartbeats 800000 in
omit [FiniteDimensional K L] in
lemma mk0_mapIdealGal_congr (σ : L ≃ₐ[K] L)
    {I J : nonZeroDivisors (Ideal (𝓞 L))}
    (h : ClassGroup.mk0 I = ClassGroup.mk0 J) :
    ClassGroup.mk0 (mapIdealGal K L σ I) = ClassGroup.mk0 (mapIdealGal K L σ J) := by
  rw [ClassGroup.mk0_eq_mk0_iff] at h ⊢
  obtain ⟨x, y, hx, hy, hxy⟩ := h
  let e := galRingEquiv K L σ
  refine ⟨e x, e y, fun h0 => hx (e.injective (by rwa [map_zero])),
    fun h0 => hy (e.injective (by rwa [map_zero])), ?_⟩
  show Ideal.span {e x} * Ideal.map e ↑I = Ideal.span {e y} * Ideal.map e ↑J
  rw [show Ideal.span {e x} = Ideal.map e (Ideal.span {x}) from
    by rw [Ideal.map_span]; simp [Set.image_singleton],
   show Ideal.span {e y} = Ideal.map e (Ideal.span {y}) from
    by rw [Ideal.map_span]; simp [Set.image_singleton],
   ← Ideal.map_mul, ← Ideal.map_mul, hxy]

set_option maxHeartbeats 1200000 in
def actOnClassGroup (σ : L ≃ₐ[K] L) :
    ClassGroup (𝓞 L) →* ClassGroup (𝓞 L) where
  toFun c := ClassGroup.mk0 (mapIdealGal K L σ
    (Function.surjInv ClassGroup.mk0_surjective c))
  map_one' := by
    rw [mk0_mapIdealGal_congr K L σ
        ((Function.surjInv_eq (ClassGroup.mk0_surjective (R := 𝓞 L)) 1).trans
          ClassGroup.mk0.map_one.symm),
      (mapIdealGal K L σ).map_one, ClassGroup.mk0.map_one]
  map_mul' c d := by
    rw [mk0_mapIdealGal_congr K L σ
        ((Function.surjInv_eq ClassGroup.mk0_surjective (c * d)).trans
          (show ClassGroup.mk0 (Function.surjInv ClassGroup.mk0_surjective c *
              Function.surjInv ClassGroup.mk0_surjective d) = c * d from by
            rw [ClassGroup.mk0.map_mul, Function.surjInv_eq ClassGroup.mk0_surjective c,
              Function.surjInv_eq ClassGroup.mk0_surjective d]).symm),
      (mapIdealGal K L σ).map_mul, ClassGroup.mk0.map_mul]

set_option maxHeartbeats 800000 in
omit [FiniteDimensional K L] in
lemma actOnClassGroup_mk0 (σ : L ≃ₐ[K] L)
    (I : nonZeroDivisors (Ideal (𝓞 L))) :
    actOnClassGroup K L σ (ClassGroup.mk0 I) =
    ClassGroup.mk0 (mapIdealGal K L σ I) :=
  mk0_mapIdealGal_congr K L σ
    (Function.surjInv_eq ClassGroup.mk0_surjective (ClassGroup.mk0 I))

set_option maxHeartbeats 1600000 in
omit [FiniteDimensional K L] in
lemma actOnClassGroup_mul (σ τ : L ≃ₐ[K] L) :
    actOnClassGroup K L (σ * τ) =
    (actOnClassGroup K L σ).comp (actOnClassGroup K L τ) := by
  ext c; obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  simp only [MonoidHom.comp_apply, actOnClassGroup_mk0]; congr 1; ext : 1
  show Ideal.map (galRingEquiv K L (σ * τ)) I.val =
    Ideal.map (galRingEquiv K L σ) (Ideal.map (galRingEquiv K L τ) I.val)
  rw [ideal_map_comp_ringEquiv, galRingEquiv_mul]

set_option maxHeartbeats 1600000 in
omit [FiniteDimensional K L] in
lemma actOnClassGroup_one :
    actOnClassGroup K L 1 = MonoidHom.id _ := by
  ext c; obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  simp only [MonoidHom.id_apply, actOnClassGroup_mk0]; congr 1; ext : 1
  show Ideal.map (galRingEquiv K L 1) I.val = I.val
  rw [galRingEquiv_one, ideal_map_refl_ringEquiv]

def classGroupMulAut (σ : L ≃ₐ[K] L) : MulAut (ClassGroup (𝓞 L)) :=
  MulEquiv.ofBijective (actOnClassGroup K L σ) ⟨
    fun a b h => by
      have := congr_arg (actOnClassGroup K L σ⁻¹) h
      simp only [← MonoidHom.comp_apply,
        show (actOnClassGroup K L σ⁻¹).comp (actOnClassGroup K L σ) = MonoidHom.id _ from
          by rw [← actOnClassGroup_mul, inv_mul_cancel, actOnClassGroup_one]] at this
      exact this,
    fun b => ⟨actOnClassGroup K L σ⁻¹ b, by
      show (actOnClassGroup K L σ).comp (actOnClassGroup K L σ⁻¹) b = b
      rw [← actOnClassGroup_mul, mul_inv_cancel, actOnClassGroup_one]; rfl⟩⟩

set_option maxHeartbeats 1600000 in
def classGroupAutHom :
    (L ≃ₐ[K] L) →* MulAut (ClassGroup (𝓞 L)) where
  toFun := classGroupMulAut K L
  map_one' := by
    ext x; show (actOnClassGroup K L 1) x = x
    rw [actOnClassGroup_one]; rfl
  map_mul' σ τ := by
    ext x
    show (actOnClassGroup K L (σ * τ)) x =
      (classGroupMulAut K L σ) ((classGroupMulAut K L τ) x)
    rw [actOnClassGroup_mul]; rfl

end GaloisClassGroupAction

instance galActsOnClassGroup (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L] :
    MulDistribMulAction (L ≃ₐ[K] L) (ClassGroup (𝓞 L)) :=
  MulDistribMulAction.compHom (ClassGroup (𝓞 L)) (classGroupAutHom K L)

def classGroupFixed (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L] :
    Subgroup (ClassGroup (𝓞 L)) :=
  FixedPoints.subgroup (L ≃ₐ[K] L) (ClassGroup (𝓞 L))

def normImageUnits (K L : Type*) [Field K] [Field L] [Algebra K L] :
    Subgroup (𝓞 K)ˣ :=
  Subgroup.comap (Units.map (algebraMap (𝓞 K) K).toMonoidHom)
    (MonoidHom.range (Units.map (Algebra.norm K : L →* K)))

noncomputable def normUnitsIndex (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L] : ℕ :=
  (normImageUnits K L).index

def normIntegerUnits (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] : Subgroup (𝓞 K)ˣ :=
  Subgroup.comap (Units.map (algebraMap (𝓞 K) K).toMonoidHom)
    (MonoidHom.range (Units.map ((Algebra.norm K).comp (algebraMap (𝓞 L) L).toMonoidHom)))

noncomputable def principalFixedIndex (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    [IsCyclic (L ≃ₐ[K] L)] : ℕ :=
  (normIntegerUnits K L).index * Module.finrank K L / e_inf K L

structure RamificationData where
  e₀ : ℕ
  e_inf : ℕ
  e₀_pos : 0 < e₀
  e_inf_pos : 0 < e_inf

def RamificationData.e (rd : RamificationData) : ℕ := rd.e₀ * rd.e_inf

def RamificationData.IsTotallyUnramified (rd : RamificationData) : Prop :=
  rd.e = 1

structure CyclicExtensionData where
  G : Type*
  M : Type*
  [instGroupG : Group G]
  [instFiniteG : Finite G]
  [instCyclicG : IsCyclic G]
  [instCommGroupM : CommGroup M]
  [instFiniteM : Finite M]
  [instAction : MulDistribMulAction G M]
  n : ℕ
  hn_pos : 0 < n
  hn_eq : n = Nat.card G
  ram : RamificationData
  card_ClK : ℕ
  hcard_ClK_pos : 0 < card_ClK
  norm_units_index : ℕ
  hnorm_pos : 0 < norm_units_index
  norm_index_IK : ℕ
  hnorm_index_IK_pos : 0 < norm_index_IK
  h0_ClL : ℕ
  hh0_pos : 0 < h0_ClL
  h_acnf : Nat.card (FixedPoints.subgroup G M) * norm_units_index * n = ram.e * card_ClK
  h_norm_index_ineq : norm_index_IK ≤ n
  h_eq8 : norm_index_IK * ram.e = h0_ClL * norm_units_index * n

attribute [instance] CyclicExtensionData.instGroupG
  CyclicExtensionData.instFiniteG CyclicExtensionData.instCyclicG
  CyclicExtensionData.instCommGroupM CyclicExtensionData.instFiniteM
  CyclicExtensionData.instAction

def CyclicExtensionData.card_ClL_G (d : CyclicExtensionData) : ℕ :=
  Nat.card (FixedPoints.subgroup d.G d.M)

lemma _root_.Ideal.spanNorm_mem_nonZeroDivisors
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    {I : Ideal (𝓞 L)} (hI : I ∈ nonZeroDivisors (Ideal (𝓞 L))) :
    Ideal.spanNorm (𝓞 K) I ∈ nonZeroDivisors (Ideal (𝓞 K)) := by
  rw [mem_nonZeroDivisors_iff_ne_zero] at hI ⊢
  intro h; apply hI
  rwa [show (0 : Ideal (𝓞 K)) = ⊥ from rfl, Ideal.spanNorm_eq_bot_iff,
       show (⊥ : Ideal (𝓞 L)) = 0 from rfl] at h

def spanNormNZD (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] :
    (nonZeroDivisors (Ideal (𝓞 L))) →* (nonZeroDivisors (Ideal (𝓞 K))) where
  toFun I := ⟨Ideal.spanNorm (𝓞 K) I.1, Ideal.spanNorm_mem_nonZeroDivisors I.2⟩
  map_one' := by ext; simp
  map_mul' := fun I J => by ext; simp

def normToClK (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] :
    (nonZeroDivisors (Ideal (𝓞 L))) →* ClassGroup (𝓞 K) :=
  ClassGroup.mk0.comp (spanNormNZD K L)

lemma normToClK_well_defined
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    {I J : nonZeroDivisors (Ideal (𝓞 L))}
    (h : ClassGroup.mk0 I = ClassGroup.mk0 J) :
    normToClK K L I = normToClK K L J := by
  rw [ClassGroup.mk0_eq_mk0_iff] at h
  obtain ⟨x, y, hx, hy, heq⟩ := h
  have heq' : Ideal.spanNorm (𝓞 K) (Ideal.span {x} * I.val) =
               Ideal.spanNorm (𝓞 K) (Ideal.span {y} * J.val) := by rw [heq]
  rw [Ideal.spanNorm_mul, Ideal.spanNorm_mul, Ideal.spanNorm_singleton,
      Ideal.spanNorm_singleton] at heq'
  unfold normToClK spanNormNZD
  simp only [MonoidHom.comp_apply, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [ClassGroup.mk0_eq_mk0_iff]
  exact ⟨_, _, by rwa [ne_eq, Algebra.intNorm_eq_zero],
         by rwa [ne_eq, Algebra.intNorm_eq_zero], heq'⟩

lemma normToClK_of_mk0_eq_one
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    {I : nonZeroDivisors (Ideal (𝓞 L))} (h : ClassGroup.mk0 I = 1) :
    normToClK K L I = 1 := by
  have h' : ClassGroup.mk0 I =
      ClassGroup.mk0 ⟨⊤, by rw [mem_nonZeroDivisors_iff_ne_zero]; exact top_ne_bot⟩ := by
    rw [h]; symm; rw [ClassGroup.mk0_eq_one_iff]
    exact ⟨1, by simp [Ideal.span_singleton_one]⟩
  rw [normToClK_well_defined h']
  show ClassGroup.mk0 (spanNormNZD K L ⟨⊤, _⟩) = 1
  rw [ClassGroup.mk0_eq_one_iff]
  show Submodule.IsPrincipal (Ideal.spanNorm (𝓞 K) ⊤)
  rw [Ideal.spanNorm_top]
  exact ⟨1, by simp [Ideal.span_singleton_one]⟩

open FractionalIdeal in
def normOnFracUnits (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] :
    (FractionalIdeal (nonZeroDivisors (𝓞 L)) (FractionRing (𝓞 L)))ˣ →*
      ClassGroup (𝓞 K) where
  toFun I := normToClK K L ⟨ClassGroup.integralRep (I : FractionalIdeal _ _),
    ClassGroup.integralRep_mem_nonZeroDivisors I.ne_zero⟩
  map_one' :=
    normToClK_of_mk0_eq_one (by rw [ClassGroup.mk0_integralRep, map_one])
  map_mul' := fun I J => by
    have hmul : ClassGroup.mk0 (R := 𝓞 L) ⟨ClassGroup.integralRep ((I * J : _) : _),
        ClassGroup.integralRep_mem_nonZeroDivisors (I * J).ne_zero⟩ =
      ClassGroup.mk0 (⟨ClassGroup.integralRep (I : _),
        ClassGroup.integralRep_mem_nonZeroDivisors I.ne_zero⟩ *
       ⟨ClassGroup.integralRep (J : _),
        ClassGroup.integralRep_mem_nonZeroDivisors J.ne_zero⟩) := by
      rw [ClassGroup.mk0_integralRep, map_mul (ClassGroup.mk (R := 𝓞 L)),
          ← ClassGroup.mk0_integralRep I, ← ClassGroup.mk0_integralRep J, map_mul]
    show normToClK K L ⟨ClassGroup.integralRep ((I * J : _) : _), _⟩ =
      normToClK K L ⟨ClassGroup.integralRep (I : _), _⟩ *
      normToClK K L ⟨ClassGroup.integralRep (J : _), _⟩
    rw [normToClK_well_defined hmul, map_mul]

set_option maxHeartbeats 800000 in
open FractionalIdeal in
lemma normOnFracUnits_kills_principal (K L : Type*)
    [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] :
    (toPrincipalIdeal (𝓞 L) (FractionRing (𝓞 L))).range ≤
    (normOnFracUnits K L).ker := by
  intro I hI
  rw [MonoidHom.mem_ker]
  have hI1 : ClassGroup.mk I = 1 := by
    rw [ClassGroup.mk_eq_one_iff]
    obtain ⟨x, hx⟩ := hI
    rw [← hx, coe_toPrincipalIdeal]
    exact ⟨x, coe_spanSingleton _ _⟩
  show normToClK K L ⟨ClassGroup.integralRep (I : _), _⟩ = 1
  exact normToClK_of_mk0_eq_one (by rw [ClassGroup.mk0_integralRep, hI1])

def ClassGroup.normMap (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] :
    ClassGroup (𝓞 L) →* ClassGroup (𝓞 K) :=
  QuotientGroup.lift _ (normOnFracUnits K L) (normOnFracUnits_kills_principal K L)

def idealGroupIndex
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] : ℕ :=
  (MonoidHom.range (ClassGroup.normMap K L)).index

noncomputable def CyclicExtensionData.norm_index_IK_ax
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L] [IsCyclic (L ≃ₐ[K] L)] : ℕ :=
  idealGroupIndex K L

def galUnitsAutHom : (L ≃ₐ[K] L) →* MulAut (𝓞 L)ˣ where
  toFun σ := Units.mapEquiv (galRestrict (𝓞 K) K L (𝓞 L) σ).toRingEquiv
  map_one' := by ext u; simp [Units.mapEquiv, galRestrict]
  map_mul' σ τ := by ext u; simp [Units.mapEquiv, galRestrict]

instance galActsOnUnits : MulDistribMulAction (L ≃ₐ[K] L) (𝓞 L)ˣ :=
  MulDistribMulAction.compHom (𝓞 L)ˣ (galUnitsAutHom K L)

def normMapUnits [Fintype (L ≃ₐ[K] L)] : (𝓞 L)ˣ →* (𝓞 L)ˣ where
  toFun u := ∏ σ : (L ≃ₐ[K] L), σ • u
  map_one' := by simp
  map_mul' u v := by
    show ∏ σ : (L ≃ₐ[K] L), σ • (u * v) =
      (∏ σ : (L ≃ₐ[K] L), σ • u) * (∏ σ : (L ≃ₐ[K] L), σ • v)
    simp_rw [smul_mul']; exact Finset.prod_mul_distrib

def unitsFixed : Subgroup (𝓞 L)ˣ :=
  FixedPoints.subgroup (L ≃ₐ[K] L) (𝓞 L)ˣ

def normImageUnitsSubgroup [Fintype (L ≃ₐ[K] L)] : Subgroup (𝓞 L)ˣ :=
  (normMapUnits K L).range

def normKerUnits [Fintype (L ≃ₐ[K] L)] : Subgroup (𝓞 L)ˣ :=
  (normMapUnits K L).ker

def augmentationUnitsSubgroup : Subgroup (𝓞 L)ˣ :=
  Subgroup.closure {x : (𝓞 L)ˣ | ∃ (σ : L ≃ₐ[K] L) (u : (𝓞 L)ˣ), x = σ • u * u⁻¹}

lemma subgroup_fg_of_comm_fg (H : Subgroup (𝓞 L)ˣ) : H.FG := by
  rw [Subgroup.fg_iff_add_fg]
  haveI : Monoid.FG (𝓞 L)ˣ := inferInstance
  haveI : Module.Finite ℤ (Additive (𝓞 L)ˣ) := AddMonoid.FG.to_moduleFinite_int
  haveI : IsNoetherian ℤ (Additive (𝓞 L)ˣ) := isNoetherian_of_isNoetherianRing_of_finite ℤ _
  have hfg_mod : (H.toAddSubgroup.toIntSubmodule : Submodule ℤ (Additive (𝓞 L)ˣ)).FG :=
    IsNoetherian.noetherian _
  rwa [Submodule.fg_iff_addSubgroup_fg, AddSubgroup.toIntSubmodule_toAddSubgroup] at hfg_mod

lemma pow_card_mem_augmentationUnitsSubgroup [Fintype (L ≃ₐ[K] L)]
    (u : (𝓞 L)ˣ) (hu : normMapUnits K L u = 1) :
    u ^ Fintype.card (L ≃ₐ[K] L) ∈ augmentationUnitsSubgroup K L := by
  have key : u ^ Fintype.card (L ≃ₐ[K] L) = ∏ σ : (L ≃ₐ[K] L), (u * (σ • u)⁻¹) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Finset.prod_inv_distrib]
    simp only [normMapUnits, MonoidHom.coe_mk, OneHom.coe_mk] at hu
    rw [hu, inv_one, mul_one]
  rw [key]
  apply Subgroup.prod_mem
  intro σ _
  have : u * (σ • u)⁻¹ = (σ • u * u⁻¹)⁻¹ := by group
  rw [this]
  apply Subgroup.inv_mem
  apply Subgroup.subset_closure
  exact ⟨σ, u, rfl⟩

def tateH0Units [Fintype (L ≃ₐ[K] L)] : Type _ :=
  unitsFixed K L ⧸ (normImageUnitsSubgroup K L).subgroupOf (unitsFixed K L)

def tateMinus1Units [Fintype (L ≃ₐ[K] L)] : Type _ :=
  normKerUnits K L ⧸ (augmentationUnitsSubgroup K L).subgroupOf (normKerUnits K L)

instance tateH0Units.finite [Fintype (L ≃ₐ[K] L)] [IsCyclic (L ≃ₐ[K] L)] :
    Finite (tateH0Units K L) := by
  classical


  set n := Fintype.card (L ≃ₐ[K] L) with hn_def
  have hn_pos : 0 < n := Fintype.card_pos
  have hn_ne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn_pos

  haveI : Group.FG (𝓞 L)ˣ := Group.fg_iff_monoid_fg.mpr inferInstance
  haveI : Group.FG (unitsFixed K L) := by
    rw [Group.fg_iff_monoid_fg] at *
    have hfgA : AddGroup.FG (Additive (𝓞 L)ˣ) := by
      rw [AddGroup.fg_iff_addMonoid_fg]; exact Monoid.fg_iff_add_fg.mp ‹_›
    have hfgAH : AddGroup.FG (Additive ↥(unitsFixed K L)) := by
      rw [← Module.Finite.iff_addGroup_fg] at *
      exact Module.Finite.of_injective
        ((unitsFixed K L).toAddSubgroup.toIntSubmodule.subtype) Subtype.val_injective
    rw [Monoid.fg_iff_add_fg]; exact AddGroup.fg_iff_addMonoid_fg.mp hfgAH

  have hfin : (powMonoidHom (α := ↥(unitsFixed K L)) n).range.FiniteIndex :=
    Subgroup.finiteIndex_range_powMonoidHom_of_fg (unitsFixed K L) hn_ne


  have hle : (powMonoidHom (α := ↥(unitsFixed K L)) n).range ≤
      (normImageUnitsSubgroup K L).subgroupOf (unitsFixed K L) := by
    intro u hmem
    rw [MonoidHom.mem_range] at hmem
    obtain ⟨v, heq⟩ := hmem
    simp only [Subgroup.mem_subgroupOf]


    have hfixed : ∀ σ : (L ≃ₐ[K] L), σ • (v : (𝓞 L)ˣ) = (v : (𝓞 L)ˣ) := fun σ =>
      v.property σ

    have hnorm : normMapUnits K L (v : (𝓞 L)ˣ) = (v : (𝓞 L)ˣ) ^ n := by
      show ∏ σ : (L ≃ₐ[K] L), σ • (v : (𝓞 L)ˣ) = (v : (𝓞 L)ˣ) ^ n
      simp_rw [hfixed]
      rw [Finset.prod_const, Finset.card_univ, hn_def]

    have hval : (u : (𝓞 L)ˣ) = (v : (𝓞 L)ˣ) ^ n := by
      have := congr_arg Subtype.val heq
      simp [powMonoidHom_apply] at this
      exact this.symm
    rw [show (u : (𝓞 L)ˣ) = normMapUnits K L (v : (𝓞 L)ˣ) from by rw [hnorm, ← hval]]
    exact MonoidHom.mem_range.mpr ⟨(v : (𝓞 L)ˣ), rfl⟩

  haveI : ((normImageUnitsSubgroup K L).subgroupOf (unitsFixed K L)).FiniteIndex :=
    Subgroup.finiteIndex_of_le hle
  exact Subgroup.finite_quotient_of_finiteIndex

instance tateMinus1Units.finite [Fintype (L ≃ₐ[K] L)] [IsCyclic (L ≃ₐ[K] L)] :
    Finite (tateMinus1Units K L) := by
  classical

  set n := Fintype.card (L ≃ₐ[K] L) with hn_def
  have hn_ne : n ≠ 0 := Fintype.card_ne_zero

  haveI : Group.FG (𝓞 L)ˣ := Group.fg_iff_monoid_fg.mpr inferInstance
  haveI : Group.FG ↥(normKerUnits K L) :=
    (Group.fg_iff_subgroup_fg _).mpr (subgroup_fg_of_comm_fg (L := L) _)

  haveI hpow : (powMonoidHom (α := ↥(normKerUnits K L)) n).range.FiniteIndex :=
    Subgroup.finiteIndex_range_powMonoidHom_of_fg _ hn_ne


  have hle : (powMonoidHom (α := ↥(normKerUnits K L)) n).range ≤
      (augmentationUnitsSubgroup K L).subgroupOf (normKerUnits K L) := by
    intro ⟨v, hv_mem⟩ hv_range
    rw [MonoidHom.mem_range] at hv_range
    obtain ⟨⟨w, hw_mem⟩, hw_eq⟩ := hv_range
    simp only [Subgroup.mem_subgroupOf]
    have hv_eq : v = w ^ n := by
      have := congr_arg Subtype.val hw_eq
      simpa [SubgroupClass.coe_pow, powMonoidHom_apply] using this.symm
    rw [hv_eq]
    have hw_ker : normMapUnits K L w = 1 := by
      have := hw_mem
      rwa [normKerUnits, MonoidHom.mem_ker] at this
    exact pow_card_mem_augmentationUnitsSubgroup K L w hw_ker

  haveI : ((augmentationUnitsSubgroup K L).subgroupOf (normKerUnits K L)).FiniteIndex :=
    Subgroup.finiteIndex_of_le hle
  exact Subgroup.finite_quotient_of_finiteIndex

noncomputable def herbrandQuotientUnitsValue [Fintype (L ≃ₐ[K] L)]
    [IsCyclic (L ≃ₐ[K] L)] : ℚ :=
  (Nat.card (tateH0Units K L) : ℚ) / (Nat.card (tateMinus1Units K L) : ℚ)

end GaloisUnitsAction

noncomputable def algebraMapToFixed
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L] :
    (𝓞 K)ˣ →* ↥(unitsFixed K L) where
  toFun v := ⟨Units.map (algebraMap (𝓞 K) (𝓞 L)).toMonoidHom v, fun σ => by
    apply Units.val_injective
    show (galRestrict (𝓞 K) K L (𝓞 L) σ) ((algebraMap (𝓞 K) (𝓞 L)) (v : 𝓞 K)) =
         (algebraMap (𝓞 K) (𝓞 L)) (v : 𝓞 K)
    exact (galRestrict (𝓞 K) K L (𝓞 L) σ).commutes (v : 𝓞 K)⟩
  map_one' := by ext; simp
  map_mul' v w := by ext; simp

structure IdealGroupData where
  G : Type*
  I_L : Type*
  I_K : Type*
  [instGroupG : Group G]
  [instFiniteG : Finite G]
  [instCyclicG : IsCyclic G]
  [instCommGroupIL : CommGroup I_L]
  [instCommGroupIK : CommGroup I_K]
  [instAction : MulDistribMulAction G I_L]
  normMap : I_L →* I_K
  extensionMap : I_K →* I_L
  extensionMap_injective : Function.Injective extensionMap
  e₀ : ℕ
  e₀_pos : 0 < e₀
  normImage_index_pos : 0 < normMap.range.index
  extensionMap_range_le_fixedPoints : extensionMap.range ≤ FixedPoints.subgroup G I_L
  cohomNorm_eq : ∀ (I : I_L),
    (haveI := Fintype.ofFinite G; ∏ g : G, g • I) = extensionMap (normMap I)
  augmentation_preimage : ∀ (σ : G), (∀ g : G, g ∈ Subgroup.zpowers σ) →
    ∀ (I : I_L), (haveI := Fintype.ofFinite G; ∏ g : G, g • I) = 1 →
      ∃ J : I_L, σ • J * J⁻¹ = I
  index_fixedPoints_over_range :
    (extensionMap.range.subgroupOf (FixedPoints.subgroup G I_L)).index = e₀

attribute [instance] IdealGroupData.instGroupG IdealGroupData.instFiniteG
  IdealGroupData.instCyclicG IdealGroupData.instCommGroupIL
  IdealGroupData.instCommGroupIK IdealGroupData.instAction

def IdealGroupData.fixedIdeals (d : IdealGroupData) : Subgroup d.I_L :=
  FixedPoints.subgroup d.G d.I_L

def IdealGroupData.extendedIdeals (d : IdealGroupData) : Subgroup d.I_L :=
  d.extensionMap.range

def IdealGroupData.normImage (d : IdealGroupData) : Subgroup d.I_K :=
  d.normMap.range

noncomputable def IdealGroupData.cohomNormImage (d : IdealGroupData) : Subgroup d.I_L where
  carrier := Set.range (fun I : d.I_L =>
    haveI := Fintype.ofFinite d.G
    ∏ g : d.G, g • I)
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    refine ⟨a * b, ?_⟩
    simp only [smul_mul', Finset.prod_mul_distrib]
  one_mem' := ⟨1, by simp⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    refine ⟨a⁻¹, ?_⟩
    simp only [smul_inv']
    rw [Finset.prod_inv_distrib]

noncomputable def quotient_equiv_image_quotient
    {A C : Type*} [CommGroup A] [CommGroup C]
    (f : A →* C) (B : Subgroup A) (hB : f.ker ≤ B) :
    A ⧸ B ≃* ↥f.range ⧸ (B.map f).subgroupOf f.range := by
  let g : A →* ↥f.range ⧸ (B.map f).subgroupOf f.range :=
    (QuotientGroup.mk' _).comp (f.rangeRestrict)
  have hg_surj : Function.Surjective g := by
    intro q
    obtain ⟨⟨c, hc⟩, rfl⟩ := QuotientGroup.mk'_surjective _ q
    obtain ⟨a, rfl⟩ := hc
    exact ⟨a, rfl⟩
  have hg_ker : g.ker = B := by
    ext a
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, g]
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨b, hb, hfb⟩
      have hab : a * b⁻¹ ∈ f.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv]
        have : f b = f a := by
          change f b = (f.rangeRestrict a : C)
          simp only [MonoidHom.coe_rangeRestrict]
          exact hfb
        rw [this, mul_inv_cancel]
      exact Subgroup.mul_mem_cancel_right B (Subgroup.inv_mem B hb) |>.mp (hB hab)
    · intro ha
      exact ⟨a, ha, rfl⟩
  exact ((QuotientGroup.quotientMulEquivOfEq hg_ker).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective g hg_surj))

def TateCohomologyAllTrivial (G : Type*) [Group G] [Finite G]
    (M : Type*) [CommGroup M] [MulDistribMulAction G M] : Prop := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  exact (
    (∀ m : M, (∀ g : G, g • m = m) → ∃ a : M, m = ∏ g : G, g • a) ∧
    (∀ m : M, (∏ g : G, g • m) = 1 →
      m ∈ Subgroup.closure {x : M | ∃ (g : G) (a : M), x = g • a * a⁻¹}))

def galFracSubmod (σ : L ≃ₐ[K] L) (M : Submodule (𝓞 L) L) : Submodule (𝓞 L) L where
  carrier := σ '' (M : Set L)
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, add_mem ha hb, map_add σ a b⟩
  zero_mem' := ⟨0, zero_mem M, map_zero σ⟩
  smul_mem' r := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨(galRestrict (𝓞 K) K L (𝓞 L) σ).symm r • x, M.smul_mem _ hx, ?_⟩
    simp only [Algebra.smul_def, map_mul]
    congr 1; rw [← algebraMap_galRestrict_apply (𝓞 K) σ, AlgEquiv.apply_symm_apply]

noncomputable def galFracIdeal (σ : L ≃ₐ[K] L)
    (I : FractionalIdeal (𝓞 L)⁰ L) : FractionalIdeal (𝓞 L)⁰ L :=
  ⟨galFracSubmod K L σ (I : Submodule (𝓞 L) L), by
    obtain ⟨a, ha_mem, ha⟩ := I.2
    refine ⟨galRestrict (𝓞 K) K L (𝓞 L) σ a,
      map_mem_nonZeroDivisors _ (galRestrict (𝓞 K) K L (𝓞 L) σ).injective ha_mem, ?_⟩
    rintro b ⟨x, hx, rfl⟩; obtain ⟨c, hc⟩ := ha x hx
    exact ⟨galRestrict (𝓞 K) K L (𝓞 L) σ c, by
      simp only [Algebra.smul_def] at hc ⊢
      rw [algebraMap_galRestrict_apply (𝓞 K) σ,
        algebraMap_galRestrict_apply (𝓞 K) σ, ← map_mul, hc]⟩⟩

noncomputable def galFracIdealEquiv (σ : L ≃ₐ[K] L) :
    FractionalIdeal (𝓞 L)⁰ L ≃* FractionalIdeal (𝓞 L)⁰ L where
  toFun := galFracIdeal K L σ
  invFun := galFracIdeal K L σ⁻¹
  left_inv I := by
    apply FractionalIdeal.coeToSubmodule_injective
    ext x; simp only [galFracIdeal, galFracSubmod]
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩; simpa using hz
    · intro hx; exact ⟨σ x, ⟨x, hx, rfl⟩, by simp⟩
  right_inv I := by
    apply FractionalIdeal.coeToSubmodule_injective
    ext x; simp only [galFracIdeal, galFracSubmod]
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩; simpa using hz
    · intro hx; exact ⟨σ⁻¹ x, ⟨x, hx, rfl⟩, by simp⟩
  map_mul' I J := by
    apply FractionalIdeal.coeToSubmodule_injective
    simp only [galFracIdeal, FractionalIdeal.coe_mul]
    ext x; constructor
    · rintro ⟨y, hy, rfl⟩
      exact Submodule.mul_induction_on hy
        (fun a ha b hb => by
          rw [map_mul σ a b]
          exact Submodule.mul_mem_mul
            (show σ a ∈ galFracSubmod K L σ ↑I from ⟨a, ha, rfl⟩)
            (show σ b ∈ galFracSubmod K L σ ↑J from ⟨b, hb, rfl⟩))
        (fun a b ha hb => by rw [map_add]; exact add_mem ha hb)
    · intro hx
      exact Submodule.mul_induction_on hx
        (fun a ha b hb => by
          obtain ⟨a', ha', rfl⟩ := (show a ∈ galFracSubmod K L σ ↑I from ha)
          obtain ⟨b', hb', rfl⟩ := (show b ∈ galFracSubmod K L σ ↑J from hb)
          exact ⟨a' * b', Submodule.mul_mem_mul ha' hb', map_mul σ a' b'⟩)
        (fun a b ha hb => by
          obtain ⟨a', ha', rfl⟩ := ha; obtain ⟨b', hb', rfl⟩ := hb
          exact ⟨a' + b', add_mem ha' hb', map_add σ a' b'⟩)

set_option maxHeartbeats 400000 in
noncomputable def galFracIdealAutHom :
    (L ≃ₐ[K] L) →* MulAut (FractionalIdeal (𝓞 L)⁰ L) where
  toFun := galFracIdealEquiv K L
  map_one' := by
    ext I : 1
    show galFracIdeal K L 1 I = I
    apply FractionalIdeal.coeToSubmodule_injective
    ext x; simp only [galFracIdeal, galFracSubmod]
    constructor
    · rintro ⟨y, hy, rfl⟩; simpa using hy
    · intro hx; exact ⟨x, hx, by simp⟩
  map_mul' σ τ := by
    ext I : 1
    show galFracIdeal K L (σ * τ) I = galFracIdeal K L σ (galFracIdeal K L τ I)
    apply FractionalIdeal.coeToSubmodule_injective
    ext x; simp only [galFracIdeal, galFracSubmod]
    constructor
    · rintro ⟨z, hz, rfl⟩; exact ⟨τ z, ⟨z, hz, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩; exact ⟨z, hz, rfl⟩

def mulAutUnitsLift (M : Type*) [Monoid M] : MulAut M →* MulAut Mˣ where
  toFun := Units.mapEquiv
  map_one' := by ext u; simp [Units.mapEquiv]
  map_mul' f g := by ext u; simp [Units.mapEquiv]

@[reducible]
noncomputable def galActionOnFracIdealUnits_ax :
    (K : Type*) → (L : Type*) → [Field K] → [NumberField K] → [Field L] → [NumberField L] →
    [Algebra K L] → [IsGalois K L] → [FiniteDimensional K L] → [IsCyclic (L ≃ₐ[K] L)] →
    MulDistribMulAction (L ≃ₐ[K] L) (FractionalIdeal (𝓞 L)⁰ L)ˣ :=
  fun K L => MulDistribMulAction.compHom _
    ((mulAutUnitsLift _).comp (galFracIdealAutHom K L))

@[reducible]
noncomputable def galActionOnFracIdealUnits :
    MulDistribMulAction (L ≃ₐ[K] L) (FractionalIdeal (𝓞 L)⁰ L)ˣ :=
  galActionOnFracIdealUnits_ax K L

noncomputable def idealExtensionMonoidHom_ax :
    (K : Type*) → (L : Type*) → [Field K] → [NumberField K] → [Field L] → [NumberField L] →
    [Algebra K L] → [IsGalois K L] → [FiniteDimensional K L] → [IsCyclic (L ≃ₐ[K] L)] →
    (FractionalIdeal (𝓞 K)⁰ K)ˣ →* (FractionalIdeal (𝓞 L)⁰ L)ˣ :=
  fun _K L => Units.map (FractionalIdeal.extendedHomₐ L (𝓞 L)).toMonoidHom

noncomputable def idealExtensionMonoidHom :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ →* (FractionalIdeal (𝓞 L)⁰ L)ˣ :=
  idealExtensionMonoidHom_ax K L

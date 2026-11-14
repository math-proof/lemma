import Mathlib
import Def.ModularCurve_LevelOneProlongationPair
import Class.ModularCurve_GaussPencilAdapter

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

section InstanceShortcuts
open ModularCurve

end InstanceShortcuts

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve

namespace ModularCurve.PlaceSpecialization.LevelOneProlongationPair

section Core

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
  {K₁ : Type*} [Field K₁] [Algebra (AlgebraicClosure ℚ) K₁]
  [Algebra K₁ (modularFunctionFieldBar (1 * q))]
  [IsScalarTower (AlgebraicClosure ℚ) K₁ (modularFunctionFieldBar (1 * q))]

variable (R : LevelOneProlongationPair P)

variable (K₁) in

noncomputable def gaussBase : ValuationSubring K₁ :=
  R.R₁.integers.comap (algebraMap K₁ (modularFunctionFieldBar (1 * q)))

theorem mem_gaussBase_iff (x : K₁) :
    x ∈ R.gaussBase K₁ ↔ algebraMap K₁ (modularFunctionFieldBar (1 * q)) x ∈ R.R₁.integers :=
  ValuationSubring.mem_comap

theorem algebraMap_mem_gaussBase_iff (c : AlgebraicClosure ℚ) :
    algebraMap (AlgebraicClosure ℚ) K₁ c ∈ R.gaussBase K₁ ↔ c ∈ A := by
  rw [mem_gaussBase_iff, ← IsScalarTower.algebraMap_apply]
  exact R.R₁.algebraMap_mem_iff c

theorem algebraMap_gaussBase_apply (x : R.gaussBase K₁) :
    algebraMap (R.gaussBase K₁) (modularFunctionFieldBar (1 * q)) x
      = algebraMap K₁ (modularFunctionFieldBar (1 * q)) (x : K₁) := by
  rw [IsScalarTower.algebraMap_apply (R.gaussBase K₁) K₁ (modularFunctionFieldBar (1 * q))]
  rfl

variable (K₁) in
noncomputable def toIntegers₁ : R.gaussBase K₁ →+* R.R₁.integers :=
  (algebraMap K₁ (modularFunctionFieldBar (1 * q))).restrict (R.gaussBase K₁) R.R₁.integers
    fun x hx => (R.mem_gaussBase_iff x).mp hx

@[simp] theorem coe_toIntegers₁ (x : R.gaussBase K₁) :
    (R.toIntegers₁ K₁ x : modularFunctionFieldBar (1 * q)) = algebraMap K₁ _ (x : K₁) :=
  RingHom.coe_restrict_apply _ _ _ _ x

theorem algebraMap_gaussBase_mem_integers₁ (r : R.gaussBase K₁) :
    algebraMap (R.gaussBase K₁) (modularFunctionFieldBar (1 * q)) r ∈ R.R₁.integers := by
  rw [algebraMap_gaussBase_apply]; exact (R.mem_gaussBase_iff _).mp r.2

variable (K₁) in
noncomputable def gaussOrder (y f : modularFunctionFieldBar (1 * q)) :
    Subalgebra (R.gaussBase K₁) (modularFunctionFieldBar (1 * q)) :=
  Algebra.adjoin (R.gaussBase K₁) {y, f}

theorem self_mem_gaussOrder (y f : modularFunctionFieldBar (1 * q)) : f ∈ R.gaussOrder K₁ y f :=
  Algebra.subset_adjoin (Set.mem_insert_of_mem _ rfl)

theorem gen_mem_gaussOrder (y f : modularFunctionFieldBar (1 * q)) : y ∈ R.gaussOrder K₁ y f :=
  Algebra.subset_adjoin (Set.mem_insert _ _)

theorem adjoin_le_of_mem {O : ValuationSubring (modularFunctionFieldBar (1 * q))}
    (hV : ∀ r : R.gaussBase K₁, algebraMap (R.gaussBase K₁) (modularFunctionFieldBar (1 * q)) r ∈ O)
    {s : Set (modularFunctionFieldBar (1 * q))} (hs : ∀ y ∈ s, y ∈ O) :
    ∀ x ∈ Algebra.adjoin (R.gaussBase K₁) s, x ∈ O := by
  intro x hx
  induction hx using Algebra.adjoin_induction with
  | mem y hy => exact hs y hy
  | algebraMap r => exact hV r
  | add y z _ _ hy hz => exact add_mem hy hz
  | mul y z _ _ hy hz => exact mul_mem hy hz

theorem forall_mem_pair {O : ValuationSubring (modularFunctionFieldBar (1 * q))}
    {y f : modularFunctionFieldBar (1 * q)} (hy : y ∈ O) (hf : f ∈ O) :
    ∀ z ∈ ({y, f} : Set (modularFunctionFieldBar (1 * q))), z ∈ O := by
  intro z hz
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with hz | hz
  · rw [hz]; exact hy
  · rw [hz]; exact hf

theorem gaussOrder_le_integers₁ {y f : modularFunctionFieldBar (1 * q)} (hy : y ∈ R.R₁.integers) (hf : f ∈ R.R₁.integers) :
    ∀ x ∈ R.gaussOrder K₁ y f, x ∈ R.R₁.integers := fun x hx =>
  R.adjoin_le_of_mem R.algebraMap_gaussBase_mem_integers₁ (forall_mem_pair hy hf) x hx

def ResOne (R : LevelOneProlongationPair P) : Type _ := ↥(modularFunctionFieldFullC (ResidueField A) 1)

def ResTwo (R : LevelOneProlongationPair P) : Type _ := ↥(modularFunctionFieldFullC (ResidueField A) 1)

def ResOne.val (x : R.ResOne) : modularFunctionFieldFullC (ResidueField A) 1 := x
def ResTwo.val (x : R.ResTwo) : modularFunctionFieldFullC (ResidueField A) 1 := x
def ResOne.mk (x : modularFunctionFieldFullC (ResidueField A) 1) : R.ResOne := x
def ResTwo.mk (x : modularFunctionFieldFullC (ResidueField A) 1) : R.ResTwo := x

noncomputable def ResOne.valEquiv : R.ResOne ≃+* modularFunctionFieldFullC (ResidueField A) 1 := RingEquiv.refl _
noncomputable def ResTwo.valEquiv : R.ResTwo ≃+* modularFunctionFieldFullC (ResidueField A) 1 := RingEquiv.refl _

variable (K₁) in
noncomputable def resBase₁ : R.gaussBase K₁ →+* R.ResOne := R.R₁.residue.comp (R.toIntegers₁ K₁)

theorem isUnit_of_isUnit_toIntegers {O : ValuationSubring (modularFunctionFieldBar (1 * q))}
    (g : R.gaussBase K₁ →+* O)
    (hg : ∀ x : R.gaussBase K₁, (g x : modularFunctionFieldBar (1 * q)) = algebraMap K₁ _ (x : K₁))
    (hO : ∀ x : K₁, algebraMap K₁ (modularFunctionFieldBar (1 * q)) x ∈ O → x ∈ R.gaussBase K₁)
    (x : R.gaussBase K₁) (hu : IsUnit (g x)) : IsUnit x := by
  obtain ⟨u, hu⟩ := hu
  have hinv : ((u⁻¹ : Oˣ) : O) * g x = 1 := by rw [← hu, Units.inv_mul]
  have hinvF : (((u⁻¹ : Oˣ) : O) : modularFunctionFieldBar (1 * q)) * algebraMap K₁ _ (x : K₁) = 1 := by
    have := congrArg (fun z : O => (z : modularFunctionFieldBar (1 * q))) hinv
    simpa [hg] using this
  have hx0 : (x : K₁) ≠ 0 := by
    rintro h
    rw [h, map_zero, mul_zero] at hinvF
    exact zero_ne_one hinvF
  have hxinv : (x : K₁)⁻¹ ∈ R.gaussBase K₁ := by
    apply hO
    rw [map_inv₀, ← eq_inv_of_mul_eq_one_left hinvF]
    exact ((u⁻¹ : Oˣ) : O).2
  refine isUnit_iff_exists_inv.mpr ⟨⟨_, hxinv⟩, Subtype.ext ?_⟩
  show (x : K₁) * (x : K₁)⁻¹ = 1
  exact mul_inv_cancel₀ hx0

theorem resBase₁_algebraMap (a : A) :
    R.resBase₁ K₁ ⟨algebraMap (AlgebraicClosure ℚ) K₁ a, (R.algebraMap_mem_gaussBase_iff a).mpr a.2⟩
      = (show modularFunctionFieldFullC (ResidueField A) 1 →+* R.ResOne from RingHom.id _)
          (algebraMap (ResidueField A) (modularFunctionFieldFullC (ResidueField A) 1) (IsLocalRing.residue A a)) := by
  rw [← R.R₁.residue_algebraMap a]
  exact congrArg R.R₁.residue (Subtype.ext ((R.coe_toIntegers₁ _).trans
    (IsScalarTower.algebraMap_apply (AlgebraicClosure ℚ) K₁ (modularFunctionFieldBar (1 * q)) _).symm))

variable (K₁) in
noncomputable def gaussOrderToIntegers₁ {y f : modularFunctionFieldBar (1 * q)} (hy : y ∈ R.R₁.integers) (hf : f ∈ R.R₁.integers) :
    R.gaussOrder K₁ y f →+* R.R₁.integers :=
  (RingHom.id (modularFunctionFieldBar (1 * q))).restrict (R.gaussOrder K₁ y f) R.R₁.integers
    fun x hx => R.gaussOrder_le_integers₁ hy hf x hx

@[simp] theorem coe_gaussOrderToIntegers₁ {y f : modularFunctionFieldBar (1 * q)} (hy : y ∈ R.R₁.integers) (hf : f ∈ R.R₁.integers)
    (x : R.gaussOrder K₁ y f) : (R.gaussOrderToIntegers₁ K₁ hy hf x : modularFunctionFieldBar (1 * q)) = x :=
  RingHom.coe_restrict_apply _ _ _ _ x

theorem gaussOrderToIntegers₁_algebraMap {y f : modularFunctionFieldBar (1 * q)} (hy : y ∈ R.R₁.integers) (hf : f ∈ R.R₁.integers)
    (r : R.gaussBase K₁) : R.gaussOrderToIntegers₁ K₁ hy hf (algebraMap (R.gaussBase K₁) (R.gaussOrder K₁ y f) r) = R.toIntegers₁ K₁ r := by
  apply Subtype.ext
  rw [coe_gaussOrderToIntegers₁, coe_toIntegers₁, Subalgebra.coe_algebraMap, algebraMap_gaussBase_apply]

variable (K₁) in
noncomputable def rho₁ {y f : modularFunctionFieldBar (1 * q)} (hy : y ∈ R.R₁.integers) (hf : f ∈ R.R₁.integers) :
    R.gaussOrder K₁ y f →ₐ[R.gaussBase K₁] R.ResOne :=
  AlgHom.mk ((show R.R₁.integers →+* R.ResOne from R.R₁.residue).comp (R.gaussOrderToIntegers₁ K₁ hy hf)) fun r => by
    change R.R₁.residue (R.gaussOrderToIntegers₁ K₁ hy hf (algebraMap (R.gaussBase K₁) (R.gaussOrder K₁ y f) r)) = R.resBase₁ K₁ r
    rw [gaussOrderToIntegers₁_algebraMap]
    rfl

theorem rho₁_apply {y f : modularFunctionFieldBar (1 * q)} (hy : y ∈ R.R₁.integers) (hf : f ∈ R.R₁.integers) (x : R.gaussOrder K₁ y f) :
    ResOne.val R (R.rho₁ K₁ hy hf x) = R.R₁.residue (R.gaussOrderToIntegers₁ K₁ hy hf x) := rfl

variable (K₁) in

noncomputable def constToGaussBase : A →+* R.gaussBase K₁ :=
  ((algebraMap (AlgebraicClosure ℚ) K₁).comp A.subtype).codRestrict (R.gaussBase K₁)
    fun a => (R.algebraMap_mem_gaussBase_iff (a : AlgebraicClosure ℚ)).mpr a.2

@[simp] theorem coe_constToGaussBase (a : A) :
    ((R.constToGaussBase K₁ a : R.gaussBase K₁) : K₁) = algebraMap (AlgebraicClosure ℚ) K₁ a := rfl

theorem algebraMap_residueConst (a : A) :
    algebraMap (ResidueField A) (ResidueField (R.gaussBase K₁)) (IsLocalRing.residue A a)
      = IsLocalRing.residue (R.gaussBase K₁) ⟨algebraMap (AlgebraicClosure ℚ) K₁ a,
          (R.algebraMap_mem_gaussBase_iff (a : AlgebraicClosure ℚ)).mpr a.2⟩ := by
  rw [show algebraMap (ResidueField A) (ResidueField (R.gaussBase K₁))
      = IsLocalRing.ResidueField.map (R.constToGaussBase K₁) from rfl, IsLocalRing.ResidueField.map_residue]
  rfl

noncomputable def psiOne : R.ResOne →+* ↥(modularFunctionFieldC k 1) := R.ι.comp (ResOne.valEquiv R).toRingHom

noncomputable def psiTwo : R.ResTwo →+* ↥(modularFunctionFieldC k 1) := R.ι.comp (ResTwo.valEquiv R).toRingHom

theorem psiOne_apply (x : R.ResOne) : R.psiOne x = R.ι (ResOne.val R x) := rfl
theorem psiTwo_apply (x : R.ResTwo) : R.psiTwo x = R.ι (ResTwo.val R x) := rfl

variable [R.HasGaussTransport K₁]

theorem algebraMap_mem_integers₂_of_mem_gaussBase (x : K₁) (hx : x ∈ R.gaussBase K₁) :
    algebraMap K₁ (modularFunctionFieldBar (1 * q)) x ∈ R.R₂.integers :=
  HasGaussTransport.mem₂_of_mem₁ x ((R.mem_gaussBase_iff x).mp hx)

theorem mem_gaussBase_of_algebraMap_mem_integers₂ (x : K₁)
    (hx : algebraMap K₁ (modularFunctionFieldBar (1 * q)) x ∈ R.R₂.integers) : x ∈ R.gaussBase K₁ :=
  (R.mem_gaussBase_iff x).mpr (HasGaussTransport.mem₁_of_mem₂ x hx)

variable (K₁) in
noncomputable def toIntegers₂ : R.gaussBase K₁ →+* R.R₂.integers :=
  (algebraMap K₁ (modularFunctionFieldBar (1 * q))).restrict (R.gaussBase K₁) R.R₂.integers
    fun x hx => R.algebraMap_mem_integers₂_of_mem_gaussBase x hx

@[simp] theorem coe_toIntegers₂ (x : R.gaussBase K₁) :
    (R.toIntegers₂ K₁ x : modularFunctionFieldBar (1 * q)) = algebraMap K₁ _ (x : K₁) :=
  RingHom.coe_restrict_apply _ _ _ _ x

theorem algebraMap_gaussBase_mem_integers₂ (r : R.gaussBase K₁) :
    algebraMap (R.gaussBase K₁) (modularFunctionFieldBar (1 * q)) r ∈ R.R₂.integers := by
  rw [algebraMap_gaussBase_apply]; exact R.algebraMap_mem_integers₂_of_mem_gaussBase _ r.2

theorem gaussOrder_le_integers₂ {y f : modularFunctionFieldBar (1 * q)} (hy : y ∈ R.R₂.integers) (hf : f ∈ R.R₂.integers) :
    ∀ x ∈ R.gaussOrder K₁ y f, x ∈ R.R₂.integers := fun x hx =>
  R.adjoin_le_of_mem R.algebraMap_gaussBase_mem_integers₂ (forall_mem_pair hy hf) x hx

variable (K₁) in
noncomputable def resBase₂ : R.gaussBase K₁ →+* R.ResTwo := R.R₂.residue.comp (R.toIntegers₂ K₁)

theorem resBase₂_algebraMap (a : A) :
    R.resBase₂ K₁ ⟨algebraMap (AlgebraicClosure ℚ) K₁ a, (R.algebraMap_mem_gaussBase_iff a).mpr a.2⟩
      = (show modularFunctionFieldFullC (ResidueField A) 1 →+* R.ResTwo from RingHom.id _)
          (algebraMap (ResidueField A) (modularFunctionFieldFullC (ResidueField A) 1) (IsLocalRing.residue A a)) := by
  rw [← R.R₂.residue_algebraMap a]
  exact congrArg R.R₂.residue (Subtype.ext ((R.coe_toIntegers₂ _).trans
    (IsScalarTower.algebraMap_apply (AlgebraicClosure ℚ) K₁ (modularFunctionFieldBar (1 * q)) _).symm))

variable (K₁) in
noncomputable def gaussOrderToIntegers₂ {y f : modularFunctionFieldBar (1 * q)} (hy : y ∈ R.R₂.integers) (hf : f ∈ R.R₂.integers) :
    R.gaussOrder K₁ y f →+* R.R₂.integers :=
  (RingHom.id (modularFunctionFieldBar (1 * q))).restrict (R.gaussOrder K₁ y f) R.R₂.integers
    fun x hx => R.gaussOrder_le_integers₂ hy hf x hx

@[simp] theorem coe_gaussOrderToIntegers₂ {y f : modularFunctionFieldBar (1 * q)} (hy : y ∈ R.R₂.integers) (hf : f ∈ R.R₂.integers)
    (x : R.gaussOrder K₁ y f) : (R.gaussOrderToIntegers₂ K₁ hy hf x : modularFunctionFieldBar (1 * q)) = x :=
  RingHom.coe_restrict_apply _ _ _ _ x

theorem gaussOrderToIntegers₂_algebraMap {y f : modularFunctionFieldBar (1 * q)} (hy : y ∈ R.R₂.integers) (hf : f ∈ R.R₂.integers)
    (r : R.gaussBase K₁) : R.gaussOrderToIntegers₂ K₁ hy hf (algebraMap (R.gaussBase K₁) (R.gaussOrder K₁ y f) r) = R.toIntegers₂ K₁ r := by
  apply Subtype.ext
  rw [coe_gaussOrderToIntegers₂, coe_toIntegers₂, Subalgebra.coe_algebraMap, algebraMap_gaussBase_apply]

variable (K₁) in
noncomputable def rho₂ {y f : modularFunctionFieldBar (1 * q)} (hy : y ∈ R.R₂.integers) (hf : f ∈ R.R₂.integers) :
    R.gaussOrder K₁ y f →ₐ[R.gaussBase K₁] R.ResTwo :=
  AlgHom.mk ((show R.R₂.integers →+* R.ResTwo from R.R₂.residue).comp (R.gaussOrderToIntegers₂ K₁ hy hf)) fun r => by
    change R.R₂.residue (R.gaussOrderToIntegers₂ K₁ hy hf (algebraMap (R.gaussBase K₁) (R.gaussOrder K₁ y f) r)) = R.resBase₂ K₁ r
    rw [gaussOrderToIntegers₂_algebraMap]
    rfl

theorem rho₂_apply {y f : modularFunctionFieldBar (1 * q)} (hy : y ∈ R.R₂.integers) (hf : f ∈ R.R₂.integers) (x : R.gaussOrder K₁ y f) :
    ResTwo.val R (R.rho₂ K₁ hy hf x) = R.R₂.residue (R.gaussOrderToIntegers₂ K₁ hy hf x) := rfl

end Core

end ModularCurve.PlaceSpecialization.LevelOneProlongationPair

end

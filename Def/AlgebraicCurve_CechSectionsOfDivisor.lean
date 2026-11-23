module

public import Theorem.Submodule.Repartitions
public import Def.AlgebraicGeometry_TwoChartCech

@[expose] public section

set_option autoImplicit false

noncomputable section

open WithZero

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

def lSpaceOn (S : Set (Place K F)) (D : Divisor K F) : Submodule K F where
  carrier := {f | ∀ v ∈ S, v.adicValuation f ≤ exp (D v)}
  add_mem' := fun {f g} hf hg v hv =>
    (Valuation.map_add _ f g).trans (max_le (hf v hv) (hg v hv))
  zero_mem' := fun v _ => by simp
  smul_mem' := fun c f hf v hv => by
    show v.adicValuation (c • f) ≤ exp (D v)
    rw [Algebra.smul_def, map_mul]
    exact (mul_le_of_le_one_left' (v.adicValuation_algebraMap_le_one c)).trans (hf v hv)

@[reducible] def cechSections (S₀ S₁ : Set (Place K F)) (D : Divisor K F) :
    TwoChartCech.Sections (TwoChartCech.Cover.trivial K) :=
  TwoChartCech.Sections.ofSubmodules (lSpaceOn S₀ D) (lSpaceOn S₁ D) (lSpaceOn (S₀ ∩ S₁) D)
    (lSpaceOn_anti Set.inter_subset_left D) (lSpaceOn_anti Set.inter_subset_right D)

abbrev cechDiff (S₀ S₁ : Set (Place K F)) (D : Divisor K F) :
    (lSpaceOn S₀ D × lSpaceOn S₁ D) →ₗ[K] lSpaceOn (S₀ ∩ S₁) D :=
  (cechSections S₀ S₁ D).cechDiff

abbrev cechH0 (S₀ S₁ : Set (Place K F)) (D : Divisor K F) :
    Submodule K (lSpaceOn S₀ D × lSpaceOn S₁ D) :=
  LinearMap.ker (cechDiff S₀ S₁ D)

abbrev cechH1 (S₀ S₁ : Set (Place K F)) (D : Divisor K F) : Type _ :=
  lSpaceOn (S₀ ∩ S₁) D ⧸ LinearMap.range (cechDiff S₀ S₁ D)

def cechH0Equiv {S₀ S₁ : Set (Place K F)} (hcover : S₀ ∪ S₁ = Set.univ) (D : Divisor K F) :
    cechH0 S₀ S₁ D ≃ₗ[K] riemannRochSpace D where
  toFun p := ⟨((p.1.1 : lSpaceOn S₀ D) : F), by
    rw [← lSpaceOn_inf_eq_of_cover hcover]
    exact ⟨p.1.1.2, ((mem_cechH0_iff p.1).mp p.2).symm ▸ p.1.2.2⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := ⟨(⟨f, riemannRochSpace_le_lSpaceOn S₀ D f.2⟩, ⟨f, riemannRochSpace_le_lSpaceOn S₁ D f.2⟩),
    (mem_cechH0_iff _).mpr rfl⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact Subtype.ext ((mem_cechH0_iff p.1).mp p.2)
  right_inv f := rfl

section ToH1

variable (K) in
open Classical in

def offChartIndicator (S : Set (Place K F)) : ↥(repartitions K F) :=
  ⟨fun v => if v ∈ S then 0 else 1, mem_repartitions_of_finite (by
    convert Set.finite_empty
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
    split_ifs <;> simp)⟩

open Classical in
variable (K) in

def extendOffChart (S₀ : Set (Place K F)) : F →ₗ[K] ↥(repartitions K F) where
  toFun f := offChartIndicator K S₀ * algebraMap F (↥(repartitions K F)) f
  map_add' f g := by rw [map_add, mul_add]
  map_smul' c f := by
    apply Subtype.ext
    funext v
    change (offChartIndicator K S₀ : Place K F → F) v * (c • f)
        = c • ((offChartIndicator K S₀ : Place K F → F) v * f)
    rw [Algebra.smul_def, Algebra.smul_def]
    ring

open Classical in
def toH1Aux (S₀ S₁ : Set (Place K F)) (D : Divisor K F) : ↥(lSpaceOn (S₀ ∩ S₁) D) →ₗ[K] H1 D :=
  (repartitionsOf D ⊔ principalRepartitions K F).mkQ ∘ₗ extendOffChart K S₀ ∘ₗ
    (lSpaceOn (S₀ ∩ S₁) D).subtype

def cechH1ToH1 {S₀ S₁ : Set (Place K F)} (hcover : S₀ ∪ S₁ = Set.univ) (D : Divisor K F) :
    cechH1 S₀ S₁ D →ₗ[K] H1 D :=
  (LinearMap.range (cechDiff S₀ S₁ D)).liftQ (toH1Aux S₀ S₁ D) (range_cechDiff_le_ker_toH1Aux hcover D)

end ToH1

end AlgebraicCurve

end

end

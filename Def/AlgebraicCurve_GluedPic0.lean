module

public import Abbrev.AlgebraicCurve_GluedPic0
public import Class.AlgebraicCurve_DivisorClassGroup
public import Instance.AlgebraicCurve_DivisorClassGroup

@[expose] public section

set_option autoImplicit false

noncomputable section

open IsLocalRing

namespace AlgebraicCurve

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

def HasValue (g : F) (a : K) : Prop :=
  ∃ h : g ∈ v.toValuationSubring,
    residue v.toValuationSubring ⟨g, h⟩ = algebraMap K v.ResidueField a

end Place

section Glued

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

namespace GluingData

variable {K F}
variable (S : Finset (Place K F × Place K F))

def admissible : AddSubgroup (GluingData K F S) where
  carrier := {x | x.1 ∈ Divisor.degZero (K := K) (F := F) ∧
    x.2.1 ∈ Divisor.degZero (K := K) (F := F) ∧ ∀ s ∈ S, x.1 s.1 = 0 ∧ x.2.1 s.2 = 0}
  zero_mem' := ⟨zero_mem _, zero_mem _, fun _ _ => ⟨rfl, rfl⟩⟩
  add_mem' := by
    rintro x y ⟨hx₁, hx₂, hx⟩ ⟨hy₁, hy₂, hy⟩
    refine ⟨add_mem hx₁ hy₁, add_mem hx₂ hy₂, fun s hs => ⟨?_, ?_⟩⟩
    · rw [Prod.fst_add, Finsupp.add_apply, (hx s hs).1, (hy s hs).1, add_zero]
    · rw [Prod.snd_add, Prod.fst_add, Finsupp.add_apply, (hx s hs).2, (hy s hs).2, add_zero]
  neg_mem' := by
    rintro x ⟨hx₁, hx₂, hx⟩
    refine ⟨neg_mem hx₁, neg_mem hx₂, fun s hs => ⟨?_, ?_⟩⟩
    · rw [Prod.fst_neg, Finsupp.neg_apply, (hx s hs).1, neg_zero]
    · rw [Prod.snd_neg, Prod.fst_neg, Finsupp.neg_apply, (hx s hs).2, neg_zero]

def IsGluedPrincipal (x : GluingData K F S) : Prop :=
  ∃ (g₁ g₂ : F) (a b : ↥S → Kˣ), g₁ ≠ 0 ∧ g₂ ≠ 0 ∧
    (∀ v : Place K F, x.1 v = v.ord g₁) ∧ (∀ v : Place K F, x.2.1 v = v.ord g₂) ∧
    (∀ s : ↥S, (s : Place K F × Place K F).1.HasValue g₁ (a s) ∧
      (s : Place K F × Place K F).2.HasValue g₂ (b s)) ∧
    x.2.2 = fun s => Additive.ofMul (a s / b s)

def gluedPrincipal : AddSubgroup (GluingData K F S) where
  carrier := {x | IsGluedPrincipal S x}
  zero_mem' := by
    refine ⟨1, 1, 1, 1, one_ne_zero, one_ne_zero, fun v => by simp, fun v => by simp,
      fun s => ⟨?_, ?_⟩, ?_⟩
    · exact ⟨one_mem _, by
        rw [map_one]; exact map_one (residue (s : Place K F × Place K F).1.toValuationSubring)⟩
    · exact ⟨one_mem _, by
        rw [map_one]; exact map_one (residue (s : Place K F × Place K F).2.toValuationSubring)⟩
    · funext s
      simp
  add_mem' := by
    rintro x y ⟨g₁, g₂, a, b, hg₁, hg₂, hx₁, hx₂, hv, hw⟩
      ⟨g₁', g₂', a', b', hg₁', hg₂', hy₁, hy₂, hv', hw'⟩
    refine ⟨g₁ * g₁', g₂ * g₂', a * a', b * b', mul_ne_zero hg₁ hg₁', mul_ne_zero hg₂ hg₂',
      fun v => ?_, fun v => ?_, fun s => ⟨?_, ?_⟩, ?_⟩
    · rw [Prod.fst_add, Finsupp.add_apply, hx₁ v, hy₁ v, v.ord_mul hg₁ hg₁']
    · rw [Prod.snd_add, Prod.fst_add, Finsupp.add_apply, hx₂ v, hy₂ v, v.ord_mul hg₂ hg₂']
    · obtain ⟨hg, hr⟩ := (hv s).1
      obtain ⟨hg', hr'⟩ := (hv' s).1
      have hmul : (s : Place K F × Place K F).1.HasValue (g₁ * g₁') ((a s : K) * (a' s : K)) := by
        refine ⟨mul_mem hg hg', ?_⟩
        have hx : (⟨g₁ * g₁', mul_mem hg hg'⟩ : (s : Place K F × Place K F).1.toValuationSubring) =
          ⟨g₁, hg⟩ * ⟨g₁', hg'⟩ := rfl
        rw [hx, map_mul, hr, hr', map_mul]
      simpa only [Pi.mul_apply, Units.val_mul] using hmul
    · obtain ⟨hg, hr⟩ := (hv s).2
      obtain ⟨hg', hr'⟩ := (hv' s).2
      have hmul : (s : Place K F × Place K F).2.HasValue (g₂ * g₂') ((b s : K) * (b' s : K)) := by
        refine ⟨mul_mem hg hg', ?_⟩
        have hx : (⟨g₂ * g₂', mul_mem hg hg'⟩ : (s : Place K F × Place K F).2.toValuationSubring) =
          ⟨g₂, hg⟩ * ⟨g₂', hg'⟩ := rfl
        rw [hx, map_mul, hr, hr', map_mul]
      simpa only [Pi.mul_apply, Units.val_mul] using hmul
    · rw [Prod.snd_add, Prod.snd_add, hw, hw']
      funext s
      rw [Pi.add_apply, Pi.mul_apply, Pi.mul_apply, ← ofMul_mul, div_mul_div_comm]
  neg_mem' := by
    rintro x ⟨g₁, g₂, a, b, hg₁, hg₂, hx₁, hx₂, hv, hw⟩
    refine ⟨g₁⁻¹, g₂⁻¹, a⁻¹, b⁻¹, inv_ne_zero hg₁, inv_ne_zero hg₂,
      fun v => ?_, fun v => ?_, fun s => ⟨?_, ?_⟩, ?_⟩
    · rw [Prod.fst_neg, Finsupp.neg_apply, hx₁ v, v.ord_inv]
    · rw [Prod.snd_neg, Prod.fst_neg, Finsupp.neg_apply, hx₂ v, v.ord_inv]
    · obtain ⟨hg, hr⟩ := (hv s).1
      have ha : (a s : K) ≠ 0 := (a s).ne_zero
      have hunit : IsUnit (⟨g₁, hg⟩ : (s : Place K F × Place K F).1.toValuationSubring) := by
        rw [← residue_ne_zero_iff_isUnit, hr]
        exact (map_ne_zero _).mpr ha
      obtain ⟨u, hu⟩ := hunit
      have hcoe : ((u : (s : Place K F × Place K F).1.toValuationSubring) : F) = g₁ := by rw [hu]
      have hinv :
          ((((u⁻¹ : ((s : Place K F × Place K F).1.toValuationSubring)ˣ) :
            (s : Place K F × Place K F).1.toValuationSubring) : F) = g₁⁻¹) := by
        have h1 :
            g₁ *
              (((u⁻¹ : ((s : Place K F × Place K F).1.toValuationSubring)ˣ) :
                (s : Place K F × Place K F).1.toValuationSubring) : F) = 1 := by
          rw [← hcoe, ← MulMemClass.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
            OneMemClass.coe_one]
        exact (inv_eq_of_mul_eq_one_right h1).symm
      have hmem : g₁⁻¹ ∈ (s : Place K F × Place K F).1.toValuationSubring :=
        hinv ▸ SetLike.coe_mem _
      have hval : (s : Place K F × Place K F).1.HasValue g₁⁻¹ (a s)⁻¹ := by
        refine ⟨hmem, ?_⟩
        have hx : (⟨g₁⁻¹, hmem⟩ : (s : Place K F × Place K F).1.toValuationSubring)
            = ((u⁻¹ : ((s : Place K F × Place K F).1.toValuationSubring)ˣ) :
              (s : Place K F × Place K F).1.toValuationSubring) :=
          Subtype.ext hinv.symm
        rw [hx, map_units_inv, hu, hr, map_inv₀]
      simpa only [Pi.inv_apply, Units.val_inv_eq_inv_val] using hval
    · obtain ⟨hg, hr⟩ := (hv s).2
      have ha : (b s : K) ≠ 0 := (b s).ne_zero
      have hunit : IsUnit (⟨g₂, hg⟩ : (s : Place K F × Place K F).2.toValuationSubring) := by
        rw [← residue_ne_zero_iff_isUnit, hr]
        exact (map_ne_zero _).mpr ha
      obtain ⟨u, hu⟩ := hunit
      have hcoe : ((u : (s : Place K F × Place K F).2.toValuationSubring) : F) = g₂ := by rw [hu]
      have hinv :
          ((((u⁻¹ : ((s : Place K F × Place K F).2.toValuationSubring)ˣ) :
            (s : Place K F × Place K F).2.toValuationSubring) : F) = g₂⁻¹) := by
        have h1 :
            g₂ *
              (((u⁻¹ : ((s : Place K F × Place K F).2.toValuationSubring)ˣ) :
                (s : Place K F × Place K F).2.toValuationSubring) : F) = 1 := by
          rw [← hcoe, ← MulMemClass.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
            OneMemClass.coe_one]
        exact (inv_eq_of_mul_eq_one_right h1).symm
      have hmem : g₂⁻¹ ∈ (s : Place K F × Place K F).2.toValuationSubring :=
        hinv ▸ SetLike.coe_mem _
      have hval : (s : Place K F × Place K F).2.HasValue g₂⁻¹ (b s)⁻¹ := by
        refine ⟨hmem, ?_⟩
        have hx : (⟨g₂⁻¹, hmem⟩ : (s : Place K F × Place K F).2.toValuationSubring)
            = ((u⁻¹ : ((s : Place K F × Place K F).2.toValuationSubring)ˣ) :
              (s : Place K F × Place K F).2.toValuationSubring) :=
          Subtype.ext hinv.symm
        rw [hx, map_units_inv, hu, hr, map_inv₀]
      simpa only [Pi.inv_apply, Units.val_inv_eq_inv_val] using hval
    · rw [Prod.snd_neg, Prod.snd_neg, hw]
      funext s
      rw [Pi.neg_apply, Pi.inv_apply, Pi.inv_apply, inv_div_inv, ← ofMul_inv, inv_div]

end GluingData

abbrev GluedPic0 (S : Finset (Place K F × Place K F)) : Type _ :=
  ↥(GluingData.admissible S) ⧸ (GluingData.gluedPrincipal S).addSubgroupOf (GluingData.admissible S)

namespace GluedPic0

variable {K F}
variable (S : Finset (Place K F × Place K F))

def mk : ↥(GluingData.admissible S) →+ GluedPic0 K F S :=
  QuotientAddGroup.mk' _

def toPic0PairAux : ↥(GluingData.admissible S) →+ Pic0 K F × Pic0 K F where
  toFun x := (Pic0.mk ⟨(x : GluingData K F S).1, x.2.1⟩,
    Pic0.mk ⟨(x : GluingData K F S).2.1, x.2.2.1⟩)
  map_zero' := rfl
  map_add' _ _ := rfl

def toPic0Pair : GluedPic0 K F S →+ Pic0 K F × Pic0 K F :=
  QuotientAddGroup.lift _ (toPic0PairAux S) <| by
    rintro x ⟨g₁, g₂, _, _, hg₁, hg₂, h₁, h₂, -, -⟩
    rw [AddMonoidHom.mem_ker]
    exact Prod.ext ((QuotientAddGroup.eq_zero_iff _).mpr ⟨g₁, hg₁, h₁⟩)
      ((QuotientAddGroup.eq_zero_iff _).mpr ⟨g₂, hg₂, h₂⟩)

def nodeUnitAux : (↥S → Additive Kˣ) →+ ↥(GluingData.admissible S) where
  toFun w := ⟨(0, 0, w), ⟨zero_mem _, zero_mem _, fun _ _ => ⟨rfl, rfl⟩⟩⟩
  map_zero' := rfl
  map_add' _ _ := Subtype.ext <| Prod.ext (add_zero _).symm (Prod.ext (add_zero _).symm rfl)

def nodeUnit : (↥S → Additive Kˣ) →+ GluedPic0 K F S :=
  (mk S).comp (nodeUnitAux S)

end GluedPic0

end Glued

end AlgebraicCurve

end

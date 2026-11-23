module

public import Theorem.Valuation.DivisorClassGroup
public import Abbrev.AlgebraicCurve_GluedPic0

public noncomputable section

set_option autoImplicit false

noncomputable section

open IsLocalRing

namespace AlgebraicCurve

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

@[simp]
public theorem ord_algebraMap_of_constant (c : K) : v.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · have hu : IsUnit (algebraMap K v.toValuationSubring c) := hc.isUnit.map _
    have h := v.ord_coe_unit hu.unit
    rwa [IsUnit.unit_spec, coe_algebraMap] at h


public theorem residue_algebraMap (c : K) :
    residue v.toValuationSubring (algebraMap K v.toValuationSubring c)
      = algebraMap K v.ResidueField c := by
  rw [IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField c,
    ResidueField.algebraMap_eq]


public theorem hasValue_iff (g : F) (a : K) :
    v.HasValue g a ↔ ∃ h : g ∈ v.toValuationSubring,
      residue v.toValuationSubring ⟨g, h⟩ = algebraMap K v.ResidueField a :=
  Iff.rfl

variable {v}


public theorem HasValue.mem {g : F} {a : K} (h : v.HasValue g a) : g ∈ v.toValuationSubring :=
  h.1


public theorem HasValue.residue_eq {g : F} {a : K} (h : v.HasValue g a) :
    residue v.toValuationSubring ⟨g, h.mem⟩ = algebraMap K v.ResidueField a :=
  h.2

variable (v) in

public theorem hasValue_one : v.HasValue (1 : F) 1 :=
  ⟨one_mem _, by rw [map_one]; exact map_one (residue v.toValuationSubring)⟩

variable (v) in

public theorem hasValue_algebraMap (c : K) : v.HasValue (algebraMap K F c) c :=
  ⟨v.algebraMap_mem' c, v.residue_algebraMap c⟩


public theorem HasValue.mul {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g * g') (a * a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨mul_mem hg hg', ?_⟩
  have hx : (⟨g * g', mul_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ * ⟨g', hg'⟩ := rfl
  rw [hx, map_mul, hr, hr', map_mul]


public theorem HasValue.isUnit {g : F} {a : K} (h : v.HasValue g a) (ha : a ≠ 0) :
    IsUnit (⟨g, h.mem⟩ : v.toValuationSubring) := by
  rw [← residue_ne_zero_iff_isUnit, h.residue_eq]
  exact (map_ne_zero _).mpr ha


public theorem HasValue.ne_zero {g : F} {a : K} (h : v.HasValue g a) (ha : a ≠ 0) : g ≠ 0 := by
  intro hg
  apply (h.isUnit ha).ne_zero
  exact Subtype.ext hg


public theorem HasValue.inv {g : F} {a : K} (h : v.HasValue g a) (ha : a ≠ 0) :
    v.HasValue g⁻¹ a⁻¹ := by
  obtain ⟨u, hu⟩ := h.isUnit ha
  have hcoe : ((u : v.toValuationSubring) : F) = g := by rw [hu]
  have hinv : (((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) : F) = g⁻¹ := by
    have h1 : g * (((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) : F) = 1 := by
      rw [← hcoe, ← MulMemClass.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        OneMemClass.coe_one]
    exact (inv_eq_of_mul_eq_one_right h1).symm
  have hmem : g⁻¹ ∈ v.toValuationSubring := hinv ▸ SetLike.coe_mem _
  refine ⟨hmem, ?_⟩
  have hx : (⟨g⁻¹, hmem⟩ : v.toValuationSubring)
      = ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) :=
    Subtype.ext hinv.symm
  rw [hx, map_units_inv, hu, h.residue_eq, map_inv₀]


public theorem HasValue.unique {g : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g a') :
    a = a' :=
  (algebraMap K v.ResidueField).injective (h.residue_eq.symm.trans h'.residue_eq)


public theorem HasValue.ord_eq_zero {g : F} {a : K} (h : v.HasValue g a) (ha : a ≠ 0) : v.ord g = 0 := by
  have h0 := v.ord_coe_unit (h.isUnit ha).unit
  rwa [IsUnit.unit_spec] at h0

variable (v) in


public theorem exists_isUnit_of_ord_eq_zero {f : F} (hf : f ≠ 0) (h : v.ord f = 0) :
    ∃ hm : f ∈ v.toValuationSubring, IsUnit (⟨f, hm⟩ : v.toValuationSubring) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [h, zpow_zero, mul_one] at hu
  subst hu
  exact ⟨(u : v.toValuationSubring).2, u.isUnit⟩

variable (v) in


public theorem exists_hasValue_of_surjective (hv : Function.Surjective (algebraMap K v.ResidueField))
    {g : F} (hg : g ∈ v.toValuationSubring) :
    ∃ a : K, v.HasValue g a ∧ (IsUnit (⟨g, hg⟩ : v.toValuationSubring) → a ≠ 0) := by
  obtain ⟨a, ha⟩ := hv (residue v.toValuationSubring ⟨g, hg⟩)
  refine ⟨a, ⟨hg, ha.symm⟩, fun hu h0 => ?_⟩
  rw [← residue_ne_zero_iff_isUnit, ← ha, h0, map_zero] at hu
  exact hu rfl

end Place

section Glued

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

namespace GluingData

variable {K F}
variable (S : Finset (Place K F × Place K F))


public theorem mem_admissible {x : GluingData K F S} :
    x ∈ admissible S ↔ x.1 ∈ Divisor.degZero (K := K) (F := F) ∧
      x.2.1 ∈ Divisor.degZero (K := K) (F := F) ∧ ∀ s ∈ S, x.1 s.1 = 0 ∧ x.2.1 s.2 = 0 :=
  Iff.rfl


public theorem zero_zero_mem_admissible (w : ↥S → Additive Kˣ) :
    ((0, 0, w) : GluingData K F S) ∈ admissible S :=
  ⟨zero_mem _, zero_mem _, fun _ _ => ⟨rfl, rfl⟩⟩


public theorem mem_gluedPrincipal {x : GluingData K F S} :
    x ∈ gluedPrincipal S ↔ IsGluedPrincipal S x :=
  Iff.rfl

end GluingData


public theorem mk_surjective : Function.Surjective (mk S) :=
  QuotientAddGroup.mk'_surjective _


public theorem mk_eq_zero_iff (x : ↥(GluingData.admissible S)) :
    mk S x = 0 ↔ GluingData.IsGluedPrincipal S (x : GluingData K F S) :=
  QuotientAddGroup.eq_zero_iff _


public theorem mk_eq_mk_iff (x y : ↥(GluingData.admissible S)) :
    mk S x = mk S y ↔ GluingData.IsGluedPrincipal S (-(x : GluingData K F S) + y) :=
  QuotientAddGroup.eq


@[simp]
public theorem toPic0Pair_mk (x : ↥(GluingData.admissible S)) :
    toPic0Pair S (mk S x) = (Pic0.mk ⟨(x : GluingData K F S).1, x.2.1⟩,
      Pic0.mk ⟨(x : GluingData K F S).2.1, x.2.2.1⟩) :=
  rfl


public theorem nodeUnit_apply (w : ↥S → Additive Kˣ) :
    nodeUnit S w = mk S ⟨(0, 0, w), GluingData.zero_zero_mem_admissible S w⟩ :=
  rfl


@[simp]
public theorem toPic0Pair_nodeUnit (w : ↥S → Additive Kˣ) : toPic0Pair S (nodeUnit S w) = 0 :=
  rfl


public theorem toPic0Pair_comp_nodeUnit : (toPic0Pair S).comp (nodeUnit S) = 0 :=
  AddMonoidHom.ext (toPic0Pair_nodeUnit S)


public theorem nodeUnit_const (c : Kˣ) : nodeUnit S (fun _ => Additive.ofMul c) = 0 := by
  rw [nodeUnit_apply, mk_eq_zero_iff]
  refine ⟨algebraMap K F c, 1, fun _ => c, 1, (map_ne_zero _).mpr c.ne_zero, one_ne_zero,
    fun v => by simp, fun v => by simp, fun s => ⟨?_, ?_⟩, ?_⟩
  · exact (s : Place K F × Place K F).1.hasValue_algebraMap (c : K)
  · simpa using (s : Place K F × Place K F).2.hasValue_one
  · funext s
    simp

end GluedPic0

end Glued

end AlgebraicCurve

end

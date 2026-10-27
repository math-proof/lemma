import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
private noncomputable def glueSubmodule (𝔠 : Ideal B) (u : B ⧸ 𝔠) : Submodule A B where
  carrier := {x | ∃ a : A, u * Ideal.Quotient.mk 𝔠 x = Ideal.Quotient.mk 𝔠 (algebraMap A B a)}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨a, ha⟩ ⟨a', ha'⟩
    exact ⟨a + a', by rw [map_add, mul_add, ha, ha', map_add, map_add]⟩
  smul_mem' := by
    rintro r x ⟨a, ha⟩
    refine ⟨r * a, ?_⟩
    rw [Algebra.smul_def, map_mul, mul_left_comm, ha, ← map_mul, ← map_mul]
variable (𝔠 : Ideal B)
private lemma mem_glueSubmodule {u : B ⧸ 𝔠} {x : B} : x ∈ glueSubmodule (A := A) 𝔠 u ↔
      ∃ a : A, u * Ideal.Quotient.mk 𝔠 x = Ideal.Quotient.mk 𝔠 (algebraMap A B a) :=
  Iff.rfl
private lemma mem_glueSubmodule_of_mem {u : B ⧸ 𝔠} {x : B} (hx : x ∈ 𝔠) : x ∈ glueSubmodule (A := A) 𝔠 u :=
  ⟨0, by rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, mul_zero, map_zero, map_zero]⟩
private lemma glueSubmodule_mul_le (u v : B ⧸ 𝔠) : glueSubmodule (A := A) 𝔠 u * glueSubmodule 𝔠 v ≤ glueSubmodule 𝔠 (u * v) := by
  rw [Submodule.mul_le]
  rintro x ⟨a, ha⟩ y ⟨b, hb⟩
  refine ⟨a * b, ?_⟩
  rw [map_mul, mul_mul_mul_comm, ha, hb, ← map_mul, ← map_mul]
variable {𝔠}
variable (h𝔠 : ∀ b ∈ 𝔠, b ∈ Set.range (algebraMap A B))
include h𝔠
private lemma exists_eq_of_mk_eq {x : B} {a : A} (h : Ideal.Quotient.mk 𝔠 x = Ideal.Quotient.mk 𝔠 (algebraMap A B a)) : ∃ a' : A, algebraMap A B a' = x := by
  rw [Ideal.Quotient.eq] at h
  obtain ⟨c, hc⟩ := h𝔠 _ h
  exact ⟨a + c, by rw [map_add, hc, add_sub_cancel]⟩
private lemma glueSubmodule_one : glueSubmodule (A := A) 𝔠 1 = 1 := by
  ext x
  rw [mem_glueSubmodule, Submodule.mem_one]
  constructor
  ·
    rintro ⟨a, ha⟩
    rw [one_mul] at ha
    apply exists_eq_of_mk_eq h𝔠 ha
  ·
    rintro ⟨a, rfl⟩
    exact ⟨a, by rw [one_mul]⟩
private lemma le_glueSubmodule_mul (u : Units (B ⧸ 𝔠)) : (𝔠.restrictScalars A : Submodule A B) ≤ glueSubmodule (A := A) 𝔠 (u : B ⧸ 𝔠) * glueSubmodule 𝔠 (↑u⁻¹ : B ⧸ 𝔠) := by
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (↑u⁻¹ : B ⧸ 𝔠)
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (u : B ⧸ 𝔠)
  have hxmem : x ∈ glueSubmodule (A := A) 𝔠 (u : B ⧸ 𝔠) :=
    ⟨1, by rw [hx, Units.mul_inv, map_one, map_one]⟩
  have hymem : y ∈ glueSubmodule (A := A) 𝔠 (↑u⁻¹ : B ⧸ 𝔠) :=
    ⟨1, by rw [hy, Units.inv_mul, map_one, map_one]⟩
  have hc : x * y - 1 ∈ 𝔠 := by
    rw [← Ideal.Quotient.eq, map_mul, hx, hy, Units.inv_mul, map_one]
  intro z hz
  change z ∈ 𝔠 at hz
  have hz1 : z * x * y ∈ glueSubmodule (A := A) 𝔠 (u : B ⧸ 𝔠) * glueSubmodule 𝔠 (↑u⁻¹ : B ⧸ 𝔠) :=
    Submodule.mul_mem_mul (mem_glueSubmodule_of_mem 𝔠 (𝔠.mul_mem_right _ hz)) hymem
  have hz2 : z * (x * y - 1) ∈
    glueSubmodule (A := A) 𝔠 (u : B ⧸ 𝔠) * glueSubmodule 𝔠 (↑u⁻¹ : B ⧸ 𝔠) :=
    Submodule.mul_mem_mul (mem_glueSubmodule_of_mem 𝔠 hz) (mem_glueSubmodule_of_mem 𝔠 hc)
  have : z = z * x * y - z * (x * y - 1) := by ring
  rw [this]
  apply sub_mem hz1 hz2
private lemma glueSubmodule_mul_inv [FaithfulSMul A B] (u : Units (B ⧸ 𝔠)) : glueSubmodule (A := A) 𝔠 (u : B ⧸ 𝔠) * glueSubmodule 𝔠 (↑u⁻¹ : B ⧸ 𝔠) = 1 := by
  apply le_antisymm
  ·
    calc
      _ ≤ glueSubmodule (A := A) 𝔠 ((u : B ⧸ 𝔠) * ↑u⁻¹) := glueSubmodule_mul_le 𝔠 _ _
      _ = 1 := by rw [Units.mul_inv, glueSubmodule_one h𝔠]
  ·
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (↑u⁻¹ : B ⧸ 𝔠)
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (u : B ⧸ 𝔠)
    have hxmem : x ∈ glueSubmodule (A := A) 𝔠 (u : B ⧸ 𝔠) :=
      ⟨1, by rw [hx, Units.mul_inv, map_one, map_one]⟩
    have hymem : y ∈ glueSubmodule (A := A) 𝔠 (↑u⁻¹ : B ⧸ 𝔠) :=
      ⟨1, by rw [hy, Units.inv_mul, map_one, map_one]⟩
    have hc : x * y - 1 ∈ 𝔠 := by
      rw [← Ideal.Quotient.eq, map_mul, hx, hy, Units.inv_mul, map_one]
    have h1 : (1 : B) ∈
      glueSubmodule (A := A) 𝔠 (u : B ⧸ 𝔠) * glueSubmodule 𝔠 (↑u⁻¹ : B ⧸ 𝔠) := by
      have : (1 : B) = x * y - (x * y - 1) := by ring
      rw [this]
      apply sub_mem (Submodule.mul_mem_mul hxmem hymem) (le_glueSubmodule_mul h𝔠 u hc)
    rw [Submodule.one_le]
    apply h1
private noncomputable def glueUnits [FaithfulSMul A B] : Units (B ⧸ 𝔠) →* Units (Submodule A B) where
  toFun u :=
    { val := glueSubmodule 𝔠 (u : B ⧸ 𝔠)
      inv := glueSubmodule 𝔠 (↑u⁻¹ : B ⧸ 𝔠)
      val_inv := glueSubmodule_mul_inv h𝔠 u
      inv_val := by rw [mul_comm]; apply glueSubmodule_mul_inv h𝔠 u }
  map_one' := Units.ext (by simp only [Units.val_one]; apply glueSubmodule_one h𝔠)
  map_mul' u v := by
    apply Units.ext
    simp only [Units.val_mul]
    apply le_antisymm
    ·
      have h1 : glueSubmodule (A := A) 𝔠 (↑v⁻¹ : B ⧸ 𝔠) * glueSubmodule 𝔠 (v : B ⧸ 𝔠) = 1 := by
        rw [mul_comm]; apply glueSubmodule_mul_inv h𝔠 v
      calc
        _ = glueSubmodule 𝔠 ((u : B ⧸ 𝔠) * v) *
              (glueSubmodule 𝔠 (↑v⁻¹ : B ⧸ 𝔠) * glueSubmodule 𝔠 (v : B ⧸ 𝔠)) := by
            rw [h1, mul_one]
        _ = glueSubmodule 𝔠 ((u : B ⧸ 𝔠) * v) * glueSubmodule 𝔠 (↑v⁻¹ : B ⧸ 𝔠) *
              glueSubmodule 𝔠 (v : B ⧸ 𝔠) := by rw [mul_assoc]
        _ ≤ glueSubmodule 𝔠 ((u : B ⧸ 𝔠) * v * ↑v⁻¹) * glueSubmodule 𝔠 (v : B ⧸ 𝔠) :=
            Submodule.mul_le.mpr fun m hm n hn =>
              Submodule.mul_mem_mul (glueSubmodule_mul_le 𝔠 _ _ hm) hn
        _ = glueSubmodule 𝔠 (u : B ⧸ 𝔠) * glueSubmodule 𝔠 (v : B ⧸ 𝔠) := by
          rw [Units.mul_inv_cancel_right]
    · apply glueSubmodule_mul_le 𝔠 _ _
@[simp] private lemma val_glueUnits [FaithfulSMul A B] (u : Units (B ⧸ 𝔠)) :
  (glueUnits h𝔠 u : Submodule A B) = glueSubmodule 𝔠 (u : B ⧸ 𝔠) := rfl
private noncomputable def boundary [FaithfulSMul A B] : Units (B ⧸ 𝔠) →* CommRing.Pic A :=
  (Submodule.unitsToPic A B).comp (glueUnits h𝔠)
private lemma boundary_apply [FaithfulSMul A B] (u : Units (B ⧸ 𝔠)) : boundary h𝔠 u = Submodule.unitsToPic A B (glueUnits h𝔠 u) := rfl
private noncomputable def boundaryEquiv [FaithfulSMul A B] (u : Units (B ⧸ 𝔠)) : (boundary h𝔠 u : CommRing.Pic A) ≃ₗ[A] ↥(glueSubmodule (A := A) 𝔠 (u : B ⧸ 𝔠)) :=
  Submodule.unitsToPicEquiv (glueUnits h𝔠 u)
private lemma glueSubmodule_eq_span_of_eq [FaithfulSMul A B] (u : B ⧸ 𝔠) (s : Units B) (a : Units (A ⧸ Ideal.comap (algebraMap A B) 𝔠)) (hu : u = Ideal.quotientMap 𝔠 (algebraMap A B) le_rfl (a : A ⧸ Ideal.comap (algebraMap A B) 𝔠) * Ideal.Quotient.mk 𝔠 (s : B)) : glueSubmodule (A := A) 𝔠 u = Submodule.span A {((s⁻¹ : Units B) : B)} := by
  obtain ⟨a₀, ha₀⟩ := Ideal.Quotient.mk_surjective (a : A ⧸ Ideal.comap (algebraMap A B) 𝔠)
  obtain ⟨a₁, ha₁⟩ := Ideal.Quotient.mk_surjective (↑a⁻¹ : A ⧸ Ideal.comap (algebraMap A B) 𝔠)
  have h01 : Ideal.Quotient.mk 𝔠 (algebraMap A B a₁) * Ideal.Quotient.mk 𝔠 (algebraMap A B a₀) = 1 := by
    rw [← Ideal.quotientMap_mk (I := 𝔠) (f := algebraMap A B) (H := le_rfl),
      ← Ideal.quotientMap_mk (I := 𝔠) (f := algebraMap A B) (H := le_rfl), ha₀, ha₁, ← map_mul,
      Units.inv_mul, map_one]
  ext x
  rw [mem_glueSubmodule, Submodule.mem_span_singleton]
  constructor
  ·
    rintro ⟨c, hc⟩
    rw [hu, ← ha₀, Ideal.quotientMap_mk] at hc
    have hc' : Ideal.Quotient.mk 𝔠 ((s : B) * x) =
        Ideal.Quotient.mk 𝔠 (algebraMap A B (a₁ * c)) := by
      have := congrArg (fun z => Ideal.Quotient.mk 𝔠 (algebraMap A B a₁) * z) hc
      rw [← mul_assoc, ← mul_assoc, h01, one_mul, ← map_mul, ← map_mul, ← map_mul] at this
      apply this
    obtain ⟨a', ha'⟩ := exists_eq_of_mk_eq h𝔠 hc'
    refine ⟨a', ?_⟩
    rw [Algebra.smul_def, ha', mul_comm, Units.inv_mul_cancel_left]
  ·
    rintro ⟨c, rfl⟩
    refine ⟨a₀ * c, ?_⟩
    rw [hu, ← ha₀, Ideal.quotientMap_mk, Algebra.smul_def, ← map_mul, ← map_mul,
      mul_mul_mul_comm, Units.mul_inv, mul_one, ← map_mul]
private lemma boundary_eq_one_iff [FaithfulSMul A B] (u : Units (B ⧸ 𝔠)) : boundary h𝔠 u = 1 ↔ ∃ (t : Units B) (a : Units (A ⧸ Ideal.comap (algebraMap A B) 𝔠)), (u : B ⧸ 𝔠) = Ideal.quotientMap 𝔠 (algebraMap A B) le_rfl (a : A ⧸ Ideal.comap (algebraMap A B) 𝔠) * Ideal.Quotient.mk 𝔠 (t : B) := by
  have hker : boundary h𝔠 u = 1 ↔
      glueUnits h𝔠 u ∈ (Units.map (Submodule.spanSingleton A).toMonoidHom).range := by
    rw [← Submodule.ker_unitsToPic A B, MonoidHom.mem_ker]; rfl
  rw [hker]
  constructor
  ·
    rintro ⟨t, ht⟩
    have hval : Submodule.span A {(t : B)} = glueSubmodule (A := A) 𝔠 (u : B ⧸ 𝔠) := by
      simpa using congrArg (fun w : Units (Submodule A B) => (w : Submodule A B)) ht
    have hinv : Submodule.span A {((t⁻¹ : Units B) : B)} =
        glueSubmodule (A := A) 𝔠 (↑u⁻¹ : B ⧸ 𝔠) := by
      have h__af := (congrArg (fun w : Units (Submodule A B) => (w : Submodule A B)) (congrArg (·⁻¹) ht))
      simp at h__af
      apply h__af
    have ht_mem : (t : B) ∈ glueSubmodule (A := A) 𝔠 (u : B ⧸ 𝔠) :=
      hval ▸ Submodule.mem_span_singleton_self _
    have hti_mem : ((t⁻¹ : Units B) : B) ∈ glueSubmodule (A := A) 𝔠 (↑u⁻¹ : B ⧸ 𝔠) :=
      hinv ▸ Submodule.mem_span_singleton_self _
    obtain ⟨a₀, ha₀⟩ := ht_mem
    obtain ⟨a₁, ha₁⟩ := hti_mem
    have hprod : Ideal.Quotient.mk (Ideal.comap (algebraMap A B) 𝔠) a₀ * Ideal.Quotient.mk (Ideal.comap (algebraMap A B) 𝔠) a₁ = 1 := by
      apply Ideal.quotientMap_injective (I := 𝔠) (f := algebraMap A B)
      rw [map_mul, map_one, Ideal.quotientMap_mk, Ideal.quotientMap_mk, ← ha₀, ← ha₁,
        mul_mul_mul_comm, Units.mul_inv, one_mul, ← map_mul, Units.mul_inv, map_one]
    refine ⟨t⁻¹, ⟨Ideal.Quotient.mk (Ideal.comap (algebraMap A B) 𝔠) a₀, Ideal.Quotient.mk (Ideal.comap (algebraMap A B) 𝔠) a₁, hprod,
      by rw [mul_comm]; apply hprod⟩, ?_⟩
    change (u : B ⧸ 𝔠) = Ideal.quotientMap 𝔠 (algebraMap A B) le_rfl (Ideal.Quotient.mk (Ideal.comap (algebraMap A B) 𝔠) a₀) *
      Ideal.Quotient.mk 𝔠 ((t⁻¹ : Units B) : B)
    rw [Ideal.quotientMap_mk, ← ha₀, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]
  ·
    rintro ⟨s, a, hu⟩
    refine ⟨s⁻¹, Units.ext ?_⟩
    change Submodule.span A {((s⁻¹ : Units B) : B)} = glueSubmodule 𝔠 (u : B ⧸ 𝔠)
    rw [glueSubmodule_eq_span_of_eq h𝔠 (u : B ⧸ 𝔠) s a hu]
private lemma exists_unit_eq (hinj : Function.Injective (algebraMap A B)) (t : Units B) (a : Units (A ⧸ Ideal.comap (algebraMap A B) 𝔠)) (h : Ideal.Quotient.mk 𝔠 (t : B) = Ideal.quotientMap 𝔠 (algebraMap A B) le_rfl (a : A ⧸ Ideal.comap (algebraMap A B) 𝔠)) : ∃ s : Units A, algebraMap A B s = t := by
  obtain ⟨a₀, ha₀⟩ := Ideal.Quotient.mk_surjective (a : A ⧸ Ideal.comap (algebraMap A B) 𝔠)
  obtain ⟨a₁, ha₁⟩ := Ideal.Quotient.mk_surjective (↑a⁻¹ : A ⧸ Ideal.comap (algebraMap A B) 𝔠)
  have h1 : Ideal.Quotient.mk 𝔠 (t : B) *
      Ideal.quotientMap 𝔠 (algebraMap A B) le_rfl (↑a⁻¹ : A ⧸ Ideal.comap (algebraMap A B) 𝔠) = 1 := by
    rw [h, ← map_mul, Units.mul_inv, map_one]
  have h' : Ideal.Quotient.mk 𝔠 ((t⁻¹ : Units B) : B) =
      Ideal.quotientMap 𝔠 (algebraMap A B) le_rfl (↑a⁻¹ : A ⧸ Ideal.comap (algebraMap A B) 𝔠) := calc
      _ = Ideal.Quotient.mk 𝔠 ((t⁻¹ : Units B) : B) * (Ideal.Quotient.mk 𝔠 (t : B) *
            Ideal.quotientMap 𝔠 (algebraMap A B) le_rfl (↑a⁻¹ : A ⧸ Ideal.comap (algebraMap A B) 𝔠)) := by
        rw [h1, mul_one]
      _ = Ideal.quotientMap 𝔠 (algebraMap A B) le_rfl (↑a⁻¹ : A ⧸ Ideal.comap (algebraMap A B) 𝔠) := by
        rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
  rw [← ha₀, Ideal.quotientMap_mk] at h
  rw [← ha₁, Ideal.quotientMap_mk] at h'
  obtain ⟨s₀, hs₀⟩ := exists_eq_of_mk_eq h𝔠 h
  obtain ⟨s₁, hs₁⟩ := exists_eq_of_mk_eq h𝔠 h'
  have hmul : s₀ * s₁ = 1 := hinj (by rw [map_mul, hs₀, hs₁, Units.mul_inv, map_one])
  exact ⟨⟨s₀, s₁, hmul, by rw [mul_comm]; apply hmul⟩, hs₀⟩
private lemma mapAlgebra_boundary [FaithfulSMul A B] (u : Units (B ⧸ 𝔠)) : CommRing.Pic.mapAlgebra A B (boundary h𝔠 u) = 1 := by
  have : boundary h𝔠 u ∈ (Submodule.unitsToPic A B).range := ⟨glueUnits h𝔠 u, rfl⟩
  rw [Submodule.range_unitsToPic] at this
  apply this
end

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable {𝔠 : Ideal B}
private lemma exists_of_coe_glueSubmodule (u : B ⧸ 𝔠) (x : ↥(glueSubmodule (A := A) 𝔠 u)) :
  ∃ a : A, u * Ideal.Quotient.mk 𝔠 (x : B) = Ideal.Quotient.mk 𝔠 (algebraMap A B a) :=
  x.2
private noncomputable def glueValueFun (u : B ⧸ 𝔠) (x : ↥(glueSubmodule (A := A) 𝔠 u)) : A ⧸ Ideal.comap (algebraMap A B) 𝔠 :=
  Ideal.Quotient.mk (Ideal.comap (algebraMap A B) 𝔠) (Classical.choose (exists_of_coe_glueSubmodule u x))
private lemma quotientMap_glueValueFun (u : B ⧸ 𝔠) (x : ↥(glueSubmodule (A := A) 𝔠 u)) :
  Ideal.quotientMap 𝔠 (algebraMap A B) le_rfl (glueValueFun u x) =
      u * Ideal.Quotient.mk 𝔠 (x : B) := by
  rw [glueValueFun, Ideal.quotientMap_mk]
  apply (Classical.choose_spec (exists_of_coe_glueSubmodule u x)).symm
private noncomputable def glueValue (u : Units (B ⧸ 𝔠)) : ↥(glueSubmodule (A := A) 𝔠 (u : B ⧸ 𝔠)) →ₗ[A] (A ⧸ Ideal.comap (algebraMap A B) 𝔠) where
  toFun := glueValueFun (u : B ⧸ 𝔠)
  map_add' x y := by
    apply Ideal.quotientMap_injective (I := 𝔠) (f := algebraMap A B)
    rw [map_add, quotientMap_glueValueFun, quotientMap_glueValueFun, quotientMap_glueValueFun,
      Submodule.coe_add, map_add, mul_add]
  map_smul' r x := by
    apply Ideal.quotientMap_injective (I := 𝔠) (f := algebraMap A B)
    rw [RingHom.id_apply, quotientMap_glueValueFun, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      map_mul, Ideal.quotientMap_mk, quotientMap_glueValueFun, Submodule.coe_smul, Algebra.smul_def,
      map_mul, mul_left_comm]
private lemma quotientMap_glueValue (u : Units (B ⧸ 𝔠)) (x : ↥(glueSubmodule (A := A) 𝔠 (u : B ⧸ 𝔠))) :
  Ideal.quotientMap 𝔠 (algebraMap A B) le_rfl (glueValue (A := A) u x) =
      (u : B ⧸ 𝔠) * Ideal.Quotient.mk 𝔠 (x : B) :=
  quotientMap_glueValueFun _ x
end

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable {𝔠 : Ideal B}
variable (h𝔠 : ∀ b ∈ 𝔠, b ∈ Set.range (algebraMap A B))
include h𝔠
private lemma mem_smul_top_of_mem [FaithfulSMul A B] (u : Units (B ⧸ 𝔠)) (x : ↥(glueSubmodule (A := A) 𝔠 (u : B ⧸ 𝔠))) (hx : (x : B) ∈ 𝔠) : x ∈ Ideal.comap (algebraMap A B) 𝔠 • (⊤ : Submodule A ↥(glueSubmodule (A := A) 𝔠 (u : B ⧸ 𝔠))) := by
  obtain ⟨x₀, hx₀⟩ := Ideal.Quotient.mk_surjective (↑u⁻¹ : B ⧸ 𝔠)
  obtain ⟨y₀, hy₀⟩ := Ideal.Quotient.mk_surjective (u : B ⧸ 𝔠)
  have hx₀mem : x₀ ∈ glueSubmodule (A := A) 𝔠 (u : B ⧸ 𝔠) :=
    ⟨1, by rw [hx₀, Units.mul_inv, map_one, map_one]⟩
  have hc : x₀ * y₀ - 1 ∈ 𝔠 := by
    rw [← Ideal.Quotient.eq, map_mul, hx₀, hy₀, Units.inv_mul, map_one]
  obtain ⟨c₁, hc₁⟩ := h𝔠 _ (𝔠.mul_mem_right y₀ hx)
  obtain ⟨c₂, hc₂⟩ := h𝔠 _ hx
  have hc₁mem : c₁ ∈ Ideal.comap (algebraMap A B) 𝔠 := by
    rw [Ideal.mem_comap, hc₁]; apply 𝔠.mul_mem_right y₀ hx
  have hc₂mem : c₂ ∈ Ideal.comap (algebraMap A B) 𝔠 := by rw [Ideal.mem_comap, hc₂]; apply hx
  set X₀ : ↥(glueSubmodule (A := A) 𝔠 (u : B ⧸ 𝔠)) := ⟨x₀, hx₀mem⟩
  set C : ↥(glueSubmodule (A := A) 𝔠 (u : B ⧸ 𝔠)) := ⟨x₀ * y₀ - 1, mem_glueSubmodule_of_mem 𝔠 hc⟩
  have hdecomp : x = c₁ • X₀ - c₂ • C := by
    apply Subtype.ext
    rw [Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_smul, Algebra.smul_def,
      Algebra.smul_def, hc₁, hc₂]
    change (x : B) = _ * x₀ - _ * (x₀ * y₀ - 1)
    ring
  rw [hdecomp]
  apply sub_mem (Submodule.smul_mem_smul hc₁mem Submodule.mem_top)
    (Submodule.smul_mem_smul hc₂mem Submodule.mem_top)
private lemma bijective_liftBaseChange_glueValue [FaithfulSMul A B] (u : Units (B ⧸ 𝔠)) : Function.Bijective ((glueValue (A := A) u).liftBaseChange (A ⧸ Ideal.comap (algebraMap A B) 𝔠)) := by
  set M := ↥(glueSubmodule (A := A) 𝔠 (u : B ⧸ 𝔠))
  set Φ := (glueValue (A := A) u).liftBaseChange (A ⧸ Ideal.comap (algebraMap A B) 𝔠)
  have hsurj1 : ∀ z : (A ⧸ Ideal.comap (algebraMap A B) 𝔠) ⊗[A] M, ∃ x : M, z = 1 ⊗ₜ x := fun z => by
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _
      (TensorProduct.quotTensorEquivQuotSMul M (Ideal.comap (algebraMap A B) 𝔠) z)
    refine ⟨x, ?_⟩
    apply (TensorProduct.quotTensorEquivQuotSMul M (Ideal.comap (algebraMap A B) 𝔠)).injective
    rw [← hx, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul]
  constructor
  ·
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨x, rfl⟩ := hsurj1 z
    rw [LinearMap.liftBaseChange_tmul, one_smul] at hz
    have hx : (x : B) ∈ 𝔠 := by
      have := quotientMap_glueValue (A := A) u x
      rw [hz, map_zero, eq_comm, Units.mul_right_eq_zero, Ideal.Quotient.eq_zero_iff_mem] at this
      apply this
    have hmem := mem_smul_top_of_mem h𝔠 u x hx
    apply (TensorProduct.quotTensorEquivQuotSMul M (Ideal.comap (algebraMap A B) 𝔠)).injective
    rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, map_zero,
      Submodule.Quotient.mk_eq_zero]
    apply hmem
  ·
    obtain ⟨x₀, hx₀⟩ := Ideal.Quotient.mk_surjective (↑u⁻¹ : B ⧸ 𝔠)
    have hx₀mem : x₀ ∈ glueSubmodule (A := A) 𝔠 (u : B ⧸ 𝔠) :=
      ⟨1, by rw [hx₀, Units.mul_inv, map_one, map_one]⟩
    have hval : glueValue (A := A) u ⟨x₀, hx₀mem⟩ = 1 := by
      apply Ideal.quotientMap_injective (I := 𝔠) (f := algebraMap A B)
      rw [quotientMap_glueValue, map_one]
      change (u : B ⧸ 𝔠) * Ideal.Quotient.mk 𝔠 x₀ = 1
      rw [hx₀, Units.mul_inv]
    intro a
    refine ⟨a ⊗ₜ ⟨x₀, hx₀mem⟩, ?_⟩
    rw [LinearMap.liftBaseChange_tmul, hval, smul_eq_mul, mul_one]
private lemma mapAlgebra_quotient_boundary [FaithfulSMul A B] (u : Units (B ⧸ 𝔠)) : CommRing.Pic.mapAlgebra A (A ⧸ Ideal.comap (algebraMap A B) 𝔠) (boundary h𝔠 u) = 1 := by
  rw [CommRing.Pic.mapAlgebra_apply, CommRing.Pic.mk_eq_one_iff]
  exact ⟨LinearEquiv.trans (LinearEquiv.baseChange A (A ⧸ Ideal.comap (algebraMap A B) 𝔠) _ _ (boundaryEquiv h𝔠 u))
    (LinearEquiv.ofBijective _ (bijective_liftBaseChange_glueValue h𝔠 u))⟩
private lemma exists_glueSubmodule_eq [FaithfulSMul A B] (J : Submodule A B) (hJB : ⊤ * J = ⊤) (hfree : Nonempty ((A ⧸ Ideal.comap (algebraMap A B) 𝔠) ⊗[A] ↥J ≃ₗ[A ⧸ Ideal.comap (algebraMap A B) 𝔠] (A ⧸ Ideal.comap (algebraMap A B) 𝔠))) : ∃ u : Units (B ⧸ 𝔠), glueSubmodule (A := A) 𝔠 (u : B ⧸ 𝔠) = J := by
  obtain ⟨e'⟩ := hfree
  set q := TensorProduct.quotTensorEquivQuotSMul ↥J (Ideal.comap (algebraMap A B) 𝔠)
  obtain ⟨g, hg⟩ := Submodule.Quotient.mk_surjective _ (q (e'.symm 1))
  have hg' : e'.symm 1 = 1 ⊗ₜ g := by
    apply q.injective; rw [← hg, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul]
  have hsmul : ∀ y : ↥J, y ∈ Ideal.comap (algebraMap A B) 𝔠 • (⊤ : Submodule A ↥J) → (y : B) ∈ 𝔠 := by
    intro y hy
    refine Submodule.smul_induction_on hy (fun c hc j _ => ?_) (fun y z hy hz => ?_)
    ·
      rw [Submodule.coe_smul, Algebra.smul_def]
      apply 𝔠.mul_mem_right _ (Ideal.mem_comap.mp hc)
    ·
      rw [Submodule.coe_add]
      apply add_mem hy hz
  have star : ∀ x : ↥J, ∃ a : A, (x : B) - algebraMap A B a * g ∈ 𝔠 := by
    intro x
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (e' (1 ⊗ₜ x))
    refine ⟨a, ?_⟩
    have h1 : (1 : A ⧸ Ideal.comap (algebraMap A B) 𝔠) ⊗ₜ[A] x = Ideal.Quotient.mk (Ideal.comap (algebraMap A B) 𝔠) a ⊗ₜ[A] g := calc
      _ = e'.symm (e' (1 ⊗ₜ x)) := (e'.symm_apply_apply _).symm
        _ = e'.symm (Ideal.Quotient.mk (Ideal.comap (algebraMap A B) 𝔠) a • 1) := by rw [← ha, smul_eq_mul, mul_one]
        _ = Ideal.Quotient.mk (Ideal.comap (algebraMap A B) 𝔠) a • (1 ⊗ₜ g) := by rw [map_smul, hg']
        _ = Ideal.Quotient.mk (Ideal.comap (algebraMap A B) 𝔠) a ⊗ₜ[A] g := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have h2 : Submodule.Quotient.mk (p := Ideal.comap (algebraMap A B) 𝔠 • (⊤ : Submodule A ↥J)) x =
        Submodule.Quotient.mk (a • g) := by
      rw [← TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, h1,
        TensorProduct.quotTensorEquivQuotSMul_mk_tmul]
    rw [Submodule.Quotient.eq] at h2
    have := hsmul _ h2
    rwa [Submodule.coe_sub, Submodule.coe_smul, Algebra.smul_def] at this
  have hone : (1 : B) ∈ ⊤ * J := by rw [hJB]; apply Submodule.mem_top
  have hunit : IsUnit (Ideal.Quotient.mk 𝔠 (g : B)) := by
    have key : ∀ r ∈ ⊤ * J, ∃ y : B ⧸ 𝔠, Ideal.Quotient.mk 𝔠 r = y * Ideal.Quotient.mk 𝔠 (g : B) := by
      intro r hr
      refine Submodule.mul_induction_on hr (fun m _ n hn => ?_) (fun x y hx hy => ?_)
      ·
        obtain ⟨a, ha⟩ := star ⟨n, hn⟩
        refine ⟨Ideal.Quotient.mk 𝔠 m * Ideal.Quotient.mk 𝔠 (algebraMap A B a), ?_⟩
        rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem] at ha
        change Ideal.Quotient.mk 𝔠 n = _ at ha
        rw [map_mul (Ideal.Quotient.mk 𝔠) m n, ha, map_mul (Ideal.Quotient.mk 𝔠) _ (g : B),
          mul_assoc]
      ·
        obtain ⟨y₁, h₁⟩ := hx
        obtain ⟨y₂, h₂⟩ := hy
        exact ⟨y₁ + y₂, by rw [map_add, h₁, h₂, add_mul]⟩
    obtain ⟨y, hy⟩ := key 1 hone
    rw [map_one] at hy
    apply IsUnit.of_mul_eq_one_right _ hy.symm
  have hcJ : ∀ c ∈ 𝔠, c ∈ J := by
    intro c hc
    have key : ∀ r ∈ ⊤ * J, c * r ∈ J := by
      intro r hr
      refine Submodule.mul_induction_on hr (fun m _ n hn => ?_) (fun x y hx hy => ?_)
      ·
        obtain ⟨c', hc'⟩ := h𝔠 _ (𝔠.mul_mem_right m hc)
        rw [← mul_assoc, ← hc', ← Algebra.smul_def]
        apply J.smul_mem c' hn
      ·
        rw [mul_add]
        apply add_mem hx hy
    simpa using key 1 hone
  refine ⟨hunit.unit⁻¹, ?_⟩
  ext x
  rw [mem_glueSubmodule]
  constructor
  ·
    rintro ⟨a, ha⟩
    rw [Units.inv_mul_eq_iff_eq_mul, IsUnit.unit_spec, ← map_mul, mul_comm,
      Ideal.Quotient.mk_eq_mk_iff_sub_mem] at ha
    have : x = (x - algebraMap A B a * g) + a • (g : B) := by rw [Algebra.smul_def]; ring
    rw [this]
    apply add_mem (hcJ _ ha) (J.smul_mem a g.2)
  ·
    intro hx
    obtain ⟨a, ha⟩ := star ⟨x, hx⟩
    refine ⟨a, ?_⟩
    rw [Units.inv_mul_eq_iff_eq_mul, IsUnit.unit_spec, ← map_mul, mul_comm,
      Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    apply ha
private lemma exists_boundary_eq [FaithfulSMul A B] (P : CommRing.Pic A) (hB : CommRing.Pic.mapAlgebra A B P = 1) (hA : CommRing.Pic.mapAlgebra A (A ⧸ Ideal.comap (algebraMap A B) 𝔠) P = 1) : ∃ u, boundary h𝔠 u = P := by
  rw [CommRing.Pic.mapAlgebra_apply, CommRing.Pic.mk_eq_one_iff] at hB hA
  obtain ⟨e⟩ := hB
  set J := Module.Flat.submoduleAlgebra e
  have eJ : ↥J ≃ₗ[A] ↥P := Module.Flat.submoduleAlgebraEquiv e
  have hJB : ⊤ * J = ⊤ := Module.Flat.top_mul_submoduleAlgebra e
  have hfree : Nonempty ((A ⧸ Ideal.comap (algebraMap A B) 𝔠) ⊗[A] ↥J ≃ₗ[A ⧸ Ideal.comap (algebraMap A B) 𝔠] (A ⧸ Ideal.comap (algebraMap A B) 𝔠)) :=
    ⟨LinearEquiv.trans (LinearEquiv.baseChange A (A ⧸ Ideal.comap (algebraMap A B) 𝔠) _ _ eJ) hA.some⟩
  obtain ⟨u, hu⟩ := exists_glueSubmodule_eq h𝔠 J hJB hfree
  refine ⟨u, ?_⟩
  rw [boundary_apply, Submodule.unitsToPic_apply, CommRing.Pic.mk_eq_iff]
  exact ⟨LinearEquiv.trans (LinearEquiv.ofEq _ _ hu) eJ⟩
end

/--
[CommRing_Pic_exists_boundaryHom_conductorSquare_exact](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CommRing_Pic_exists_boundaryHom_conductorSquare_exact.lean)
-/
@[path]
private lemma main
  {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] [FaithfulSMul A B]
    (𝔠 : Ideal B) (h𝔠 : ∀ b ∈ 𝔠, b ∈ Set.range (algebraMap A B)) :
    -- imply
    ∃ δ : Units (B ⧸ 𝔠) →* CommRing.Pic A,
      (∀ u : Units (B ⧸ 𝔠), ∃ I : Submodule A B,
        (∀ x : B, x ∈ I ↔ ∃ a : A,
          (u : B ⧸ 𝔠) * Ideal.Quotient.mk 𝔠 x = Ideal.Quotient.mk 𝔠 (algebraMap A B a)) ∧
        Nonempty ((δ u : CommRing.Pic A) ≃ₗ[A] ↥I)) ∧
      (∀ u : Units (B ⧸ 𝔠), δ u = 1 ↔
        ∃ (t : Units B) (a : Units (A ⧸ 𝔠.comap (algebraMap A B))),
          (u : B ⧸ 𝔠) =
            Ideal.quotientMap 𝔠 (algebraMap A B) le_rfl (a : A ⧸ 𝔠.comap (algebraMap A B)) *
              Ideal.Quotient.mk 𝔠 (t : B)) ∧
      (∀ P : CommRing.Pic A, (∃ u, δ u = P) ↔
        CommRing.Pic.mapAlgebra A B P = 1 ∧
          CommRing.Pic.mapAlgebra A (A ⧸ 𝔠.comap (algebraMap A B)) P = 1) ∧
      (∀ (t : Units B) (a : Units (A ⧸ 𝔠.comap (algebraMap A B))),
        Ideal.Quotient.mk 𝔠 (t : B) =
            Ideal.quotientMap 𝔠 (algebraMap A B) le_rfl (a : A ⧸ 𝔠.comap (algebraMap A B)) →
          ∃ s : Units A, algebraMap A B s = t) := by
    -- proof
  refine ⟨boundary h𝔠, fun u => ⟨_, fun x => Iff.rfl, ⟨boundaryEquiv h𝔠 u⟩⟩,
    boundary_eq_one_iff h𝔠, fun P => ?_,
    fun t a h => exists_unit_eq h𝔠 (FaithfulSMul.algebraMap_injective A B) t a h⟩
  constructor
  ·
    rintro ⟨u, rfl⟩
    exact ⟨mapAlgebra_boundary h𝔠 u, mapAlgebra_quotient_boundary h𝔠 u⟩
  ·
    rintro ⟨hB, hA⟩
    apply exists_boundary_eq h𝔠 P hB hA


-- created on 2026-10-20

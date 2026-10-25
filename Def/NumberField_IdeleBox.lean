import Mathlib
import Def.IsDedekindDomain_FiniteUnitIdelesOutside

set_option autoImplicit false

namespace IsDedekindDomain.FiniteAdeleRing

variable (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

noncomputable def unitsComponent (v : HeightOneSpectrum R) :
    (FiniteAdeleRing R K)ˣ →* (v.adicCompletion K)ˣ :=
  Units.map (RestrictedProduct.evalRingHom
    (fun v : HeightOneSpectrum R => v.adicCompletion K) v).toMonoidHom


def ideleBox (S : Set (HeightOneSpectrum R)) (H : (v : HeightOneSpectrum R) → Subgroup (v.adicCompletion K)ˣ) :
    Subgroup (FiniteAdeleRing R K)ˣ where
  carrier := {x | (∀ v ∈ S, unitsComponent R K v x ∈ H v) ∧
    ∀ v : HeightOneSpectrum R, v ∉ S →
      (x : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K ∧
        ((x⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K}
  one_mem' := ⟨fun v _ => by rw [map_one]; exact one_mem _,
    fun v _ => ⟨by rw [Units.val_one]; exact one_mem _, by rw [inv_one, Units.val_one]; exact one_mem _⟩⟩
  mul_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨fun v hv => by rw [map_mul]; exact mul_mem (hx1 v hv) (hy1 v hv), fun v hv => ?_⟩
    obtain ⟨hx, hx'⟩ := hx2 v hv
    obtain ⟨hy, hy'⟩ := hy2 v hv
    exact ⟨by rw [Units.val_mul]; exact mul_mem hx hy, by rw [mul_inv, Units.val_mul]; exact mul_mem hx' hy'⟩
  inv_mem' := by
    rintro x ⟨hx1, hx2⟩
    exact ⟨fun v hv => by rw [map_inv]; exact inv_mem (hx1 v hv),
      fun v hv => ⟨(hx2 v hv).2, by rw [inv_inv]; exact (hx2 v hv).1⟩⟩

end IsDedekindDomain.FiniteAdeleRing

namespace NumberField.AdeleRing

variable (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

noncomputable def finitePartUnits : (AdeleRing R K)ˣ →* (IsDedekindDomain.FiniteAdeleRing R K)ˣ :=
  Units.map (RingHom.snd (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing R K)).toMonoidHom


noncomputable def finiteUnitsComponent (v : IsDedekindDomain.HeightOneSpectrum R) :
    (AdeleRing R K)ˣ →* (v.adicCompletion K)ˣ :=
  (IsDedekindDomain.FiniteAdeleRing.unitsComponent R K v).comp (finitePartUnits R K)

noncomputable def infiniteUnitsComponent (w : InfinitePlace K) : (AdeleRing R K)ˣ →* (w.Completion)ˣ :=
  Units.map ((Pi.evalRingHom (fun w : InfinitePlace K => w.Completion) w).comp
    (RingHom.fst (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing R K))).toMonoidHom


def ideleBox (S : Set (IsDedekindDomain.HeightOneSpectrum R))
    (H : (v : IsDedekindDomain.HeightOneSpectrum R) → Subgroup (v.adicCompletion K)ˣ)
    (Hinf : (w : InfinitePlace K) → Subgroup (w.Completion)ˣ) : Subgroup (AdeleRing R K)ˣ where
  carrier := {x | finitePartUnits R K x ∈ IsDedekindDomain.FiniteAdeleRing.ideleBox R K S H ∧
    ∀ w : InfinitePlace K, infiniteUnitsComponent R K w x ∈ Hinf w}
  one_mem' := ⟨by rw [map_one]; exact one_mem _, fun w => by rw [map_one]; exact one_mem _⟩
  mul_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    exact ⟨by rw [map_mul]; exact mul_mem hx1 hy1, fun w => by rw [map_mul]; exact mul_mem (hx2 w) (hy2 w)⟩
  inv_mem' := by
    rintro x ⟨hx1, hx2⟩
    exact ⟨by rw [map_inv]; exact inv_mem hx1, fun w => by rw [map_inv]; exact inv_mem (hx2 w)⟩

end NumberField.AdeleRing

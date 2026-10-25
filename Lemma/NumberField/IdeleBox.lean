import Mathlib
import Lemma.IsDedekindDomain.FiniteUnitIdelesOutside
import Def.NumberField_IdeleBox

set_option autoImplicit false

namespace IsDedekindDomain.FiniteAdeleRing

variable (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]


variable {R K} in
@[simp]
theorem val_unitsComponent (v : HeightOneSpectrum R) (x : (FiniteAdeleRing R K)ˣ) :
    ((unitsComponent R K v x : (v.adicCompletion K)ˣ) : v.adicCompletion K) = (x : FiniteAdeleRing R K) v :=
  rfl

variable {R K} in
theorem val_inv_unitsComponent (v : HeightOneSpectrum R) (x : (FiniteAdeleRing R K)ˣ) :
    (((unitsComponent R K v x)⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)
      = ((x⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v :=
  rfl

variable {R K} in

theorem integer_and_inv_integer_iff_valuation_eq_one (v : HeightOneSpectrum R) (x : (FiniteAdeleRing R K)ˣ) :
    ((x : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K ∧
        ((x⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K)
      ↔ Valued.v ((x : FiniteAdeleRing R K) v) = 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers]
  have hmul : (x : FiniteAdeleRing R K) v * ((x⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v = 1 := by
    rw [← val_unitsComponent, ← val_inv_unitsComponent, Units.mul_inv]
  have hab : Valued.v ((x : FiniteAdeleRing R K) v)
      * Valued.v (((x⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v) = 1 := by
    rw [← map_mul, hmul, map_one]
  have ha0 : Valued.v ((x : FiniteAdeleRing R K) v) ≠ 0 := left_ne_zero_of_mul_eq_one hab
  rw [← inv_eq_of_mul_eq_one_right hab]
  constructor
  · rintro ⟨h1, h2⟩
    exact le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.2 ha0)).1 h2)
  · intro h
    rw [h, inv_one]
    exact ⟨le_rfl, le_rfl⟩


variable {R K} in
theorem mem_ideleBox_iff (S : Set (HeightOneSpectrum R))
    (H : (v : HeightOneSpectrum R) → Subgroup (v.adicCompletion K)ˣ) (x : (FiniteAdeleRing R K)ˣ) :
    x ∈ ideleBox R K S H ↔
      (∀ v ∈ S, unitsComponent R K v x ∈ H v) ∧
        ∀ v : HeightOneSpectrum R, v ∉ S →
          (x : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K ∧
            ((x⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K :=
  Iff.rfl

theorem ideleBox_mono {S : Set (HeightOneSpectrum R)}
    {H H' : (v : HeightOneSpectrum R) → Subgroup (v.adicCompletion K)ˣ} (h : ∀ v ∈ S, H v ≤ H' v) :
    ideleBox R K S H ≤ ideleBox R K S H' :=
  fun _ hx => ⟨fun v hv => h v hv (hx.1 v hv), hx.2⟩

theorem ideleBox_top (S : Set (HeightOneSpectrum R)) : ideleBox R K S ⊤ = unitIdelesOutside R K S :=
  Subgroup.ext fun _ => ⟨fun h => h.2, fun h => ⟨fun _ _ => Subgroup.mem_top _, h⟩⟩

theorem ideleBox_le_unitIdelesOutside (S : Set (HeightOneSpectrum R))
    (H : (v : HeightOneSpectrum R) → Subgroup (v.adicCompletion K)ˣ) :
    ideleBox R K S H ≤ unitIdelesOutside R K S :=
  fun _ hx => hx.2

end IsDedekindDomain.FiniteAdeleRing

namespace NumberField.AdeleRing

variable (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]


variable {R K} in
@[simp]
theorem val_finitePartUnits (x : (AdeleRing R K)ˣ) :
    ((finitePartUnits R K x : (IsDedekindDomain.FiniteAdeleRing R K)ˣ) : IsDedekindDomain.FiniteAdeleRing R K)
      = (x : AdeleRing R K).2 :=
  rfl


variable {R K} in
@[simp]
theorem val_finiteUnitsComponent (v : IsDedekindDomain.HeightOneSpectrum R) (x : (AdeleRing R K)ˣ) :
    ((finiteUnitsComponent R K v x : (v.adicCompletion K)ˣ) : v.adicCompletion K) = (x : AdeleRing R K).2 v :=
  rfl

variable {R K} in
@[simp]
theorem val_infiniteUnitsComponent (w : InfinitePlace K) (x : (AdeleRing R K)ˣ) :
    ((infiniteUnitsComponent R K w x : (w.Completion)ˣ) : w.Completion) = (x : AdeleRing R K).1 w :=
  rfl


variable {R K} in

theorem mem_ideleBox_iff (S : Set (IsDedekindDomain.HeightOneSpectrum R))
    (H : (v : IsDedekindDomain.HeightOneSpectrum R) → Subgroup (v.adicCompletion K)ˣ)
    (Hinf : (w : InfinitePlace K) → Subgroup (w.Completion)ˣ) (x : (AdeleRing R K)ˣ) :
    x ∈ ideleBox R K S H Hinf ↔
      ((∀ v ∈ S, finiteUnitsComponent R K v x ∈ H v) ∧
        ∀ v : IsDedekindDomain.HeightOneSpectrum R, v ∉ S →
          (x : AdeleRing R K).2 v ∈ v.adicCompletionIntegers K ∧
            ((x⁻¹ : (AdeleRing R K)ˣ) : AdeleRing R K).2 v ∈ v.adicCompletionIntegers K) ∧
      ∀ w : InfinitePlace K, infiniteUnitsComponent R K w x ∈ Hinf w :=
  Iff.rfl

theorem ideleBox_mono {S : Set (IsDedekindDomain.HeightOneSpectrum R)}
    {H H' : (v : IsDedekindDomain.HeightOneSpectrum R) → Subgroup (v.adicCompletion K)ˣ}
    {Hinf Hinf' : (w : InfinitePlace K) → Subgroup (w.Completion)ˣ}
    (h : ∀ v ∈ S, H v ≤ H' v) (hinf : ∀ w, Hinf w ≤ Hinf' w) :
    ideleBox R K S H Hinf ≤ ideleBox R K S H' Hinf' :=
  fun _ hx => ⟨IsDedekindDomain.FiniteAdeleRing.ideleBox_mono R K h hx.1, fun w => hinf w (hx.2 w)⟩

theorem ideleBox_top_top (S : Set (IsDedekindDomain.HeightOneSpectrum R)) :
    ideleBox R K S ⊤ ⊤ = unitIdelesOutside R K S :=
  Subgroup.ext fun _ =>
    ⟨fun h => (IsDedekindDomain.FiniteAdeleRing.ideleBox_top R K S).le h.1,
      fun h => ⟨(IsDedekindDomain.FiniteAdeleRing.ideleBox_top R K S).ge h, fun _ => Subgroup.mem_top _⟩⟩

theorem ideleBox_le_unitIdelesOutside (S : Set (IsDedekindDomain.HeightOneSpectrum R))
    (H : (v : IsDedekindDomain.HeightOneSpectrum R) → Subgroup (v.adicCompletion K)ˣ)
    (Hinf : (w : InfinitePlace K) → Subgroup (w.Completion)ˣ) :
    ideleBox R K S H Hinf ≤ unitIdelesOutside R K S :=
  fun _ hx => IsDedekindDomain.FiniteAdeleRing.ideleBox_le_unitIdelesOutside R K S H hx.1

end NumberField.AdeleRing

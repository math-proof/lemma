import Lemma.AutomorphicForm.SmoothAutomorphicFnAt
import Lemma.AutomorphicForm.HeckeEigensystemMap
import Structure.LocalLanglands_HeckeCosetSystem
import Structure.AutomorphicForm_SmoothCuspRealization

open IsDedekindDomain NumberField MeasureTheory Matrix
open AutomorphicForm HeckeIntegralSeam

noncomputable section

namespace AutomorphicForm

variable (F : Type) [Field F] [NumberField F]

namespace SmoothCusp


theorem heckeCosetSum_const {n : ℕ} (reps : Fin n → AdelicGL2 (𝓞 F) F) (c : ℂ)
    (g : AdelicGL2 (𝓞 F) F) :
    heckeCosetSum F reps (fun _ => c) g = (n : ℂ) * c := by
  simp [heckeCosetSum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem heckeCosetSum_mul_right {n : ℕ} {U : Subgroup (AdelicGL2 (𝓞 F) F)}
    {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hinv : ∀ g : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, φ (g * u) = φ g)
    (reps : Fin n → AdelicGL2 (𝓞 F) F) (u : Fin n → AdelicGL2 (𝓞 F) F)
    (hu : ∀ i, u i ∈ U) (g : AdelicGL2 (𝓞 F) F) :
    heckeCosetSum F (fun i => reps i * u i) φ g = heckeCosetSum F reps φ g := by
  unfold heckeCosetSum
  congr 1; ext i
  rw [← mul_assoc]
  exact hinv (g * reps i) (u i) (hu i)


end SmoothCusp

open SmoothCusp


def smoothCuspNotionOf
    (pins : ∀ (F : Type) [Field F] [NumberField F], CarrierPins F) :
    CuspidalityNotion ℂ where
  IsCusp := fun F _i1 _i2 Φ => Nonempty (@SmoothCuspRealizationAt F _i1 _i2 (pins F) Φ)

def IsSmoothCuspRealizable (pins : CarrierPins F) (Φ : HeckeEigensystem F ℂ) : Prop :=
  Nonempty (SmoothCuspRealizationAt F pins Φ)

theorem isSmoothCuspRealizable_iff (pins : CarrierPins F) (Φ : HeckeEigensystem F ℂ) :
    IsSmoothCuspRealizable F pins Φ ↔ Nonempty (SmoothCuspRealizationAt F pins Φ) := Iff.rfl

theorem smoothCuspNotionOf_isCusp_iff
    (pins : ∀ (F : Type) [Field F] [NumberField F], CarrierPins F)
    (Φ : HeckeEigensystem F ℂ) :
    (smoothCuspNotionOf pins).IsCusp F Φ ↔ IsSmoothCuspRealizable F (pins F) Φ := Iff.rfl

def IsSmoothCuspRealizableVia (pins : CarrierPins F) {R : Type*} [CommRing R]
    (ι : R →+* ℂ) (Φ : HeckeEigensystem F R) : Prop :=
  IsSmoothCuspRealizable F pins (Φ.map ι)

theorem isSmoothCuspRealizableVia_id (pins : CarrierPins F) (Φ : HeckeEigensystem F ℂ) :
    IsSmoothCuspRealizableVia F pins (RingHom.id ℂ) Φ ↔ IsSmoothCuspRealizable F pins Φ := by
  unfold IsSmoothCuspRealizableVia; rw [HeckeEigensystem.map_id]

variable {F}

theorem SmoothCuspRealizationAt.toFun_ne_zero {pins : CarrierPins F}
    {Φ : HeckeEigensystem F ℂ} (R : SmoothCuspRealizationAt F pins Φ) :
    R.toFun ≠ fun _ => 0 := by
  obtain ⟨g, hg⟩ := R.exists_ne_zero
  intro h; exact hg (congrFun h g)

theorem SmoothCuspRealizationAt.left_invariant {pins : CarrierPins F}
    {Φ : HeckeEigensystem F ℂ} (R : SmoothCuspRealizationAt F pins Φ)
    (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F) :
    R.toFun (globalPoints (𝓞 F) F γ * g) = R.toFun g := by
  letI := pins.mS
  exact (((lsXiMemberAt_iff (𝓞 F) F pins.μ pins.Z R.centralChar pins.D R.toFun).mp
    R.smoothCusp.1.1).1).left_invariant γ g

theorem SmoothCuspRealizationAt.isKfSmooth {pins : CarrierPins F}
    {Φ : HeckeEigensystem F ℂ} (R : SmoothCuspRealizationAt F pins Φ) :
    IsKfSmooth F R.toFun :=
  R.smoothCusp.2

variable (F)

namespace SmoothCusp

theorem not_isHeckeCosetEigenfunctionAt_top (gv : AdelicGL2 (𝓞 F) F)
    (v : HeightOneSpectrum (𝓞 F)) (φ : AdelicGL2 (𝓞 F) F → ℂ) (c : ℂ) :
    ¬ IsHeckeCosetEigenfunctionAt F ⊤ gv v φ c := by
  rintro ⟨reps, hsys, -⟩
  haveI : Subsingleton (AdelicGL2 (𝓞 F) F ⧸ (⊤ : Subgroup (AdelicGL2 (𝓞 F) F))) :=
    QuotientGroup.subsingleton_quotient_top
  have hN : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
  have h1 : 1 < Ideal.absNorm v.asIdeal + 1 := by omega
  have heq : (0 : Fin (Ideal.absNorm v.asIdeal + 1)) = ⟨1, h1⟩ :=
    hsys.mk_injective (Subsingleton.elim _ _)
  have : (0 : ℕ) = 1 := congrArg Fin.val heq
  omega

theorem not_isHeckeCosetEigenfunctionAt_bot (gv : AdelicGL2 (𝓞 F) F)
    (v : HeightOneSpectrum (𝓞 F)) (φ : AdelicGL2 (𝓞 F) F → ℂ) (c : ℂ) :
    ¬ IsHeckeCosetEigenfunctionAt F ⊥ gv v φ c := by
  rintro ⟨reps, hsys, -⟩
  have hall : ∀ i, reps i = gv := fun i => by
    obtain ⟨u, hu, w, hw, hx⟩ := HeckePair.mem_doubleCoset_iff.mp (hsys.mem_doubleCoset i)
    rw [Subgroup.mem_bot] at hu hw
    rw [hu, hw, one_mul, mul_one] at hx; exact hx.symm
  have hN : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
  have h1 : 1 < Ideal.absNorm v.asIdeal + 1 := by omega
  have heq : (0 : Fin (Ideal.absNorm v.asIdeal + 1)) = ⟨1, h1⟩ := by
    apply hsys.mk_injective
    show QuotientGroup.mk (reps 0) = QuotientGroup.mk (reps ⟨1, h1⟩)
    rw [hall 0, hall ⟨1, h1⟩]
  have : (0 : ℕ) = 1 := congrArg Fin.val heq
  omega

end SmoothCusp

variable {F}

theorem SmoothCuspRealizationAt.level_ne_top_ne_bot {pins : CarrierPins F}
    {Φ : HeckeEigensystem F ℂ} (R : SmoothCuspRealizationAt F pins Φ)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ R.exceptionalSet) :
    pins.U Φ.level ≠ ⊤ ∧ pins.U Φ.level ≠ ⊥ :=
  ⟨fun h => not_isHeckeCosetEigenfunctionAt_top F _ v _ _ (h ▸ R.hecke_eigen v hv),
   fun h => not_isHeckeCosetEigenfunctionAt_bot F _ v _ _ (h ▸ R.hecke_eigen v hv)⟩

example (pins : ∀ (F : Type) [Field F] [NumberField F], CarrierPins F) :
    CuspidalityNotion ℂ := smoothCuspNotionOf pins

theorem SmoothCuspRealizationAt.centralChar_apply_eq {pins : CarrierPins F}
    {Φ : HeckeEigensystem F ℂ} (R : SmoothCuspRealizationAt F pins Φ)
    (z : pins.Z) {g : AdelicGL2 (𝓞 F) F} (hg : R.toFun g ≠ 0) :
    ((R.centralChar z : ℂˣ) : ℂ) =
      R.toFun (centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ) * g) / R.toFun g := by
  letI := pins.mS
  have ht := (((lsXiMemberAt_iff (𝓞 F) F pins.μ pins.Z R.centralChar pins.D R.toFun).mp
    R.smoothCusp.1.1).1).central_transform z g
  rw [ht, mul_div_assoc, div_self hg, mul_one]

theorem SmoothCuspRealizationAt.centralChar_det_gen_eq_b {pins : CarrierPins F}
    {Φ : HeckeEigensystem F ℂ} (R : SmoothCuspRealizationAt F pins Φ)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ R.exceptionalSet) (z : pins.Z)
    (hz : (z : (AdeleRing (𝓞 F) F)ˣ) = Matrix.GeneralLinearGroup.det (pins.gen v)) :
    ((R.centralChar z : ℂˣ) : ℂ) = Φ.b v := by
  obtain ⟨g, hg⟩ := R.exists_ne_zero
  rw [R.centralChar_apply_eq z hg, hz, R.central_eigen v hv g, mul_div_assoc, div_self hg,
    mul_one]

section Inhabitor

variable (F)

def degenerateZeroMeasurePins (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F) : CarrierPins F where
  mS := ⊥
  μ := 0
  D := Set.univ
  Z := ⊤
  U := U
  gen := gen
  nS := ⊥
  ν := 0

theorem isSmoothCuspAutomorphicFnAt_one_zeroMeasure
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F) :
    IsSmoothCuspAutomorphicFnAt F (degenerateZeroMeasurePins F U gen)
      (1 : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (fun _ => (1 : ℂ)) := by
  refine ⟨⟨isAutomorphicFnAt_one_trivial F _ ?_, ?_⟩, isKfSmooth_const F 1⟩
  · have hμ : (degenerateZeroMeasurePins F U gen).μ
        = (0 : @Measure _ (degenerateZeroMeasurePins F U gen).mS) := rfl
    rw [hμ]; simp only [Measure.coe_zero, Pi.zero_apply]; exact ENNReal.zero_lt_top
  · intro g
    have hν : (degenerateZeroMeasurePins F U gen).ν
        = (0 : @Measure _ (degenerateZeroMeasurePins F U gen).nS) := rfl
    rw [hν]; unfold constantTerm; exact integral_zero_measure _

def degenerateEigensystem (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) : HeckeEigensystem F ℂ where
  level := N
  level_ne_bot := hN
  a := fun v => ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) + 1
  b := fun _ => 1

@[simp] theorem degenerateEigensystem_a (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (v : HeightOneSpectrum (𝓞 F)) :
    (degenerateEigensystem F N hN).a v = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) + 1 := rfl

@[simp] theorem degenerateEigensystem_b (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (v : HeightOneSpectrum (𝓞 F)) : (degenerateEigensystem F N hN).b v = 1 := rfl

def smoothCuspRealizationAt_one_of_cosetSystems
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F) (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (hsys : ∀ v : HeightOneSpectrum (𝓞 F),
      ∃ reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 F) F,
        IsHeckeCosetSystem (U N) (gen v) reps) :
    SmoothCuspRealizationAt F (degenerateZeroMeasurePins F U gen)
      (degenerateEigensystem F N hN) where
  toFun := fun _ => 1
  exists_ne_zero := ⟨1, one_ne_zero⟩
  centralChar := 1
  smoothCusp := isSmoothCuspAutomorphicFnAt_one_zeroMeasure F U gen
  level_invariant := fun _ _ _ => rfl
  exceptionalSet := ∅
  hecke_eigen := fun v _ => by
    obtain ⟨reps, hreps⟩ := hsys v
    refine ⟨reps, hreps, fun g => ?_⟩
    rw [heckeCosetSum_const, degenerateEigensystem_a, mul_one, mul_one]
    push_cast
    ring
  central_eigen := fun v _ g => by simp only [degenerateEigensystem_b, one_mul]

end Inhabitor

end AutomorphicForm

end

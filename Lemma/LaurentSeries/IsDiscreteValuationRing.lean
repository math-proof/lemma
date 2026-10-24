import Mathlib
import sympy.Basic
open IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false


private noncomputable def hat
  {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {L : Type} [Field L] [Algebra A L] [IsFractionRing A L]
  (x : PowerSeries A) : LaurentSeries L :=
  HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))

private lemma hat_mul
  {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {L : Type} [Field L] [Algebra A L] [IsFractionRing A L]
  (x y : PowerSeries A) : hat (L := L) (x * y) = hat x * hat y := by
  simp [hat, map_mul]

private lemma hat_one
  {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {L : Type} [Field L] [Algebra A L] [IsFractionRing A L] :
  hat (L := L) (1 : PowerSeries A) = 1 := by
  simp [hat]

private lemma hat_injective
  {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {L : Type} [Field L] [Algebra A L] [IsFractionRing A L] :
  Function.Injective (hat (A := A) (L := L)) := by
  intro x y h
  have h1 := HahnSeries.ofPowerSeries_injective h
  refine PowerSeries.map_injective (algebraMap A L) (IsFractionRing.injective A L) h1

private lemma hat_ne_zero
  {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {L : Type} [Field L] [Algebra A L] [IsFractionRing A L]
  {y : PowerSeries A} (hy : y ≠ 0) : hat (L := L) y ≠ 0 := by
  intro h
  apply hy
  have h0 : hat (L := L) y = hat (L := L) (0 : PowerSeries A) := by
    rw [h]
    simp [hat]
  refine hat_injective h0

private lemma ne_zero_of_map_residue_ne_zero
  {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {y : PowerSeries A} (hy : y.map (IsLocalRing.residue A) ≠ 0) : y ≠ 0 := by
  intro h
  subst h
  refine hy (map_zero _)

private noncomputable def G
  (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {L : Type} [Field L] [Algebra A L] [IsFractionRing A L]
  (s : LaurentSeries L) : Prop :=
  ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧ s * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L)) = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))

private lemma G_iff
  {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {L : Type} [Field L] [Algebra A L] [IsFractionRing A L]
  (s : LaurentSeries L) :
  G A s ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧ s * hat y = hat x :=
  Iff.rfl

private noncomputable def GU
  (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {L : Type} [Field L] [Algebra A L] [IsFractionRing A L]
  (s : LaurentSeries L) : Prop :=
  G A s ∧ G A s⁻¹

private lemma G_one
  {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {L : Type} [Field L] [Algebra A L] [IsFractionRing A L] :
  G A (1 : LaurentSeries L) :=
  ⟨1, 1, by simp, by simp⟩

private lemma G_mul
  {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {L : Type} [Field L] [Algebra A L] [IsFractionRing A L]
  {s t : LaurentSeries L} (hs : G A s) (ht : G A t) : G A (s * t) := by
  obtain ⟨x, y, hy, hxy⟩ := (G_iff s).mp hs
  obtain ⟨x', y', hy', hxy'⟩ := (G_iff t).mp ht
  refine (G_iff _).mpr ⟨x * x', y * y', ?_, ?_⟩
  ·
    rw [map_mul]
    refine mul_ne_zero hy hy'
  ·
    rw [hat_mul, hat_mul, ← hxy, ← hxy']
    ring

private lemma GU_one
  {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {L : Type} [Field L] [Algebra A L] [IsFractionRing A L] :
  GU A (1 : LaurentSeries L) := by
  refine ⟨G_one, ?_⟩
  rw [inv_one]
  refine G_one

private lemma GU_mul
  {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {L : Type} [Field L] [Algebra A L] [IsFractionRing A L]
  {s t : LaurentSeries L} (hs : GU A s) (ht : GU A t) : GU A (s * t) := by
  refine ⟨G_mul hs.1 ht.1, ?_⟩
  rw [mul_inv]
  refine G_mul hs.2 ht.2

private lemma GU_inv
  {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {L : Type} [Field L] [Algebra A L] [IsFractionRing A L]
  {s : LaurentSeries L} (hs : GU A s) : GU A s⁻¹ := by
  refine ⟨hs.2, ?_⟩
  rw [inv_inv]
  refine hs.1

private lemma hatC_ne_zero
  {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {L : Type} [Field L] [Algebra A L] [IsFractionRing A L]
  (ϖ : A) (hϖ : Irreducible ϖ) :
  hat (L := L) (PowerSeries.C ϖ) ≠ 0 := by
  refine hat_ne_zero ?_
  intro h
  apply hϖ.ne_zero
  have this := congrArg (PowerSeries.coeff 0) h
  simp [PowerSeries.coeff_C] at this
  refine this

private lemma G_hatC
  {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {L : Type} [Field L] [Algebra A L] [IsFractionRing A L]
  (ϖ : A) : G A (hat (L := L) (PowerSeries.C ϖ)) :=
  (G_iff _).mpr ⟨PowerSeries.C ϖ, 1, by simp, by rw [hat_one, mul_one]⟩

private lemma G_hatC_pow
  {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {L : Type} [Field L] [Algebra A L] [IsFractionRing A L]
  (ϖ : A) (j : ℕ) : G A ((hat (L := L) (PowerSeries.C ϖ)) ^ j) := by
  induction j
  ·
    rw [pow_zero]
    refine G_one
  ·
    rename_i j ih
    rw [pow_succ]
    refine G_mul ih (G_hatC ϖ)

private lemma not_G_hatC_inv
  {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {L : Type} [Field L] [Algebra A L] [IsFractionRing A L]
  (ϖ : A) (hϖ : Irreducible ϖ) :
  ¬ G A ((hat (L := L) (PowerSeries.C ϖ))⁻¹) := by
  intro hG
  obtain ⟨x, y, hy, hxy⟩ := hG
  change _ * hat (L := L) y = hat x at hxy
  have hϖm : ϖ ∈ maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit
  have hϖ0 : hat (L := L) (PowerSeries.C ϖ) ≠ 0 := hatC_ne_zero ϖ hϖ
  have : hat (L := L) y = hat (PowerSeries.C ϖ * x) := by
    rw [hat_mul, ← hxy, ← mul_assoc, mul_inv_cancel₀ hϖ0, one_mul]
  have hyx : y = PowerSeries.C ϖ * x := hat_injective this
  apply hy
  rw [hyx, map_mul, PowerSeries.map_C, (IsLocalRing.residue_eq_zero_iff _).mpr hϖm]
  simp

private lemma zpow_eq_zero_of_GU
  {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {L : Type} [Field L] [Algebra A L] [IsFractionRing A L]
  (ϖ : A) (hϖ : Irreducible ϖ) {m : ℤ}
  (h : GU A ((hat (L := L) (PowerSeries.C ϖ)) ^ m)) : m = 0 := by
  have hϖ0 : hat (L := L) (PowerSeries.C ϖ) ≠ 0 := hatC_ne_zero ϖ hϖ
  refine (lt_trichotomy m 0).elim ?_ ?_
  ·
    intro hm
    exfalso
    apply not_G_hatC_inv (L := L) ϖ hϖ
    obtain ⟨j, hj⟩ : ∃ j : ℕ, m = -((j : ℤ) + 1) := ⟨(-m - 1).toNat, by omega⟩
    have : (hat (L := L) (PowerSeries.C ϖ))⁻¹ = (hat (L := L) (PowerSeries.C ϖ)) ^ j * (hat (L := L) (PowerSeries.C ϖ)) ^ m := by
      rw [hj, zpow_neg, zpow_add₀ hϖ0, zpow_one, zpow_natCast, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hϖ0), one_mul]
    rw [this]
    refine G_mul (G_hatC_pow ϖ j) h.1
  ·
    intro hm
    refine hm.elim ?_ ?_
    ·
      intro heq
      refine heq
    ·
      intro hm
      exfalso
      apply not_G_hatC_inv (L := L) ϖ hϖ
      obtain ⟨j, hj⟩ : ∃ j : ℕ, m = (j : ℤ) + 1 := ⟨(m - 1).toNat, by omega⟩
      have : (hat (L := L) (PowerSeries.C ϖ))⁻¹ = (hat (L := L) (PowerSeries.C ϖ)) ^ j * ((hat (L := L) (PowerSeries.C ϖ)) ^ m)⁻¹ := by
        rw [hj, zpow_add₀ hϖ0, zpow_one, zpow_natCast, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hϖ0), one_mul]
      rw [this]
      refine G_mul (G_hatC_pow ϖ j) h.2

private lemma exists_eq_pow_mul_GU
  {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {L : Type} [Field L] [Algebra A L] [IsFractionRing A L]
  (ϖ : A) (hϖ : Irreducible ϖ) {s : LaurentSeries L} (hs : G A s) (hs0 : s ≠ 0) :
  ∃ (k : ℕ) (u : LaurentSeries L), GU A u ∧ s = (hat (L := L) (PowerSeries.C ϖ)) ^ k * u := by
  classical
  have hϖ0 : hat (L := L) (PowerSeries.C ϖ) ≠ 0 := hatC_ne_zero ϖ hϖ
  obtain ⟨x, y, hy, hxy⟩ := (G_iff s).mp hs
  have hx0 : x ≠ 0 := by
    intro h
    apply hs0
    rw [h] at hxy
    have : hat (L := L) (0 : PowerSeries A) = 0 := by
      simp [hat]
    rw [this] at hxy
    refine (mul_eq_zero.mp hxy).resolve_right (hat_ne_zero (ne_zero_of_map_residue_ne_zero hy))
  obtain ⟨n₀, hn₀⟩ : ∃ n, PowerSeries.coeff n x ≠ 0 := by
    by_contra h
    push Not at h
    refine hx0 (PowerSeries.ext (by simp [h]))
  suffices key : ∀ (m : ℕ) (x : PowerSeries A) (s : LaurentSeries L), s * hat (L := L) y = hat x → PowerSeries.coeff n₀ x ≠ 0 → IsDiscreteValuationRing.addVal A (PowerSeries.coeff n₀ x) ≤ m → ∃ (k : ℕ) (u : LaurentSeries L), GU A u ∧ s = (hat (L := L) (PowerSeries.C ϖ)) ^ k * u by
    have hfin : IsDiscreteValuationRing.addVal A (PowerSeries.coeff n₀ x) ≠ ⊤ := by
      rw [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
      refine hn₀
    refine key _ x s hxy hn₀ (ENat.natCast_toNat hfin).symm.le
  have step : ∀ (x : PowerSeries A) (s : LaurentSeries L), s * hat (L := L) y = hat x → PowerSeries.coeff n₀ x ≠ 0 → GU A s ∨ ∃ (x' : PowerSeries A), x = PowerSeries.C ϖ * x' ∧ ((hat (L := L) (PowerSeries.C ϖ))⁻¹ * s) * hat (L := L) y = hat x' := by
    intro x s hxy hc
    classical
    have hx0 : x ≠ 0 := fun h => hc (by rw [h, map_zero])
    have hs0 : s ≠ 0 := by
      intro hs
      subst hs
      rw [zero_mul] at hxy
      refine hat_ne_zero hx0 hxy.symm
    if hG : G A s⁻¹ then
      refine Or.inl ⟨(G_iff s).mpr ⟨x, y, hy, hxy⟩, hG⟩
    else
      right
      have hxres : x.map (IsLocalRing.residue A) = 0 := by
        by_contra hx
        apply hG
        refine (G_iff _).mpr ⟨y, x, hx, ?_⟩
        rw [← hxy, ← mul_assoc, inv_mul_cancel₀ hs0, one_mul]
      have hcoef : ∀ n, ∃ c : A, PowerSeries.coeff n x = ϖ * c := by
        intro n
        have h1 : IsLocalRing.residue A (PowerSeries.coeff n x) = 0 := by
          have := congrArg (PowerSeries.coeff n) hxres
          simp [PowerSeries.coeff_map] at this
          refine this
        have h2 : PowerSeries.coeff n x ∈ maximalIdeal A := (IsLocalRing.residue_eq_zero_iff _).mp h1
        rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.mem_span_singleton'] at h2
        obtain ⟨c, hc'⟩ := h2
        refine ⟨c, by rw [← hc', mul_comm]⟩
      choose c hcc using hcoef
      refine ⟨PowerSeries.mk c, ?_, ?_⟩
      ·
        ext n
        rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hcc]
      ·
        have hxe : x = PowerSeries.C ϖ * PowerSeries.mk c := by
          ext n
          rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hcc]
        rw [mul_assoc, hxy, hxe, hat_mul, ← mul_assoc, inv_mul_cancel₀ hϖ0, one_mul]
  have hval : ∀ (x x' : PowerSeries A), x = PowerSeries.C ϖ * x' → IsDiscreteValuationRing.addVal A (PowerSeries.coeff n₀ x) = 1 + IsDiscreteValuationRing.addVal A (PowerSeries.coeff n₀ x') := by
    intro x x' h
    rw [h, PowerSeries.coeff_C_mul, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_uniformizer hϖ]
  intro m
  induction m
  ·
    intro x s hxy hc hle
    refine (step x s hxy hc).elim ?_ ?_
    ·
      intro hGU
      refine ⟨0, s, hGU, by rw [pow_zero, one_mul]⟩
    ·
      intro h
      obtain ⟨x', hx', _⟩ := h
      exfalso
      rw [hval x x' hx'] at hle
      have : (1 : ENat) ≤ 0 := le_trans le_self_add (by exact_mod_cast hle)
      refine absurd this (by decide)
  ·
    rename_i m ih
    intro x s hxy hc hle
    refine (step x s hxy hc).elim ?_ ?_
    ·
      intro hGU
      refine ⟨0, s, hGU, by rw [pow_zero, one_mul]⟩
    ·
      intro h
      obtain ⟨x', hx', hxy'⟩ := h
      have hc' : PowerSeries.coeff n₀ x' ≠ 0 := by
        intro h
        apply hc
        rw [hx', PowerSeries.coeff_C_mul, h, mul_zero]
      have hle' : IsDiscreteValuationRing.addVal A (PowerSeries.coeff n₀ x') ≤ m := by
        rw [hval x x' hx', Nat.cast_succ, add_comm] at hle
        refine (ENat.add_le_add_iff_right ENat.one_ne_top).mp hle
      obtain ⟨k, u, hu, hs'⟩ := ih x' _ hxy' hc' hle'
      refine ⟨k + 1, u, hu, ?_⟩
      rw [pow_succ', mul_assoc, ← hs', ← mul_assoc, mul_inv_cancel₀ hϖ0, one_mul]

private lemma GU_pow
  {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {L : Type} [Field L] [Algebra A L] [IsFractionRing A L]
  {s : LaurentSeries L} (hs : GU A s) (n : ℕ) : GU A (s ^ n) := by
  induction n
  ·
    rw [pow_zero]
    refine GU_one
  ·
    rename_i n ih
    rw [pow_succ]
    refine GU_mul ih hs

private lemma pow_mul_GU_inj
  {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {L : Type} [Field L] [Algebra A L] [IsFractionRing A L]
  (ϖ : A) (hϖ : Irreducible ϖ) {k k' : ℕ} {u u' : LaurentSeries L}
  (hu : GU A u) (hu' : GU A u')
  (h : (hat (L := L) (PowerSeries.C ϖ)) ^ k * u = (hat (L := L) (PowerSeries.C ϖ)) ^ k' * u')
  (h0 : u ≠ 0) : k = k' := by
  have hϖ0 : hat (L := L) (PowerSeries.C ϖ) ≠ 0 := hatC_ne_zero ϖ hϖ
  have h1 : (hat (L := L) (PowerSeries.C ϖ)) ^ ((k : ℤ) - (k' : ℤ)) = u' * u⁻¹ := by
    rw [zpow_sub₀ hϖ0, zpow_natCast, zpow_natCast, div_eq_iff (pow_ne_zero _ hϖ0)]
    calc
      _ = (hat (L := L) (PowerSeries.C ϖ)) ^ k * u * u⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ h0, mul_one]
      _ = u' * u⁻¹ * (hat (L := L) (PowerSeries.C ϖ)) ^ k' := by
        rw [h]
        ring
  have hgu : GU A ((hat (L := L) (PowerSeries.C ϖ)) ^ ((k : ℤ) - (k' : ℤ))) := by
    rw [h1]
    refine GU_mul hu' (GU_inv hu)
  have := zpow_eq_zero_of_GU (L := L) ϖ hϖ (m := (k : ℤ) - k') hgu
  omega

/--
[ValuationSubring_isDiscreteValuationRing_of_forall_mem_iff_gaussPresentation](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ValuationSubring_isDiscreteValuationRing_of_forall_mem_iff_gaussPresentation.lean)
-/
@[path]
private lemma main
  {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {L : Type} [Field L] [Algebra A L] [IsFractionRing A L]
  {E : Type} [Field E]
  (ι : E →+* LaurentSeries L)
  (W : ValuationSubring E)
  (hW : ∀ f : E, f ∈ W ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧ ι f * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L)) = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
  (hne : W ≠ ⊤) :
  -- imply
  IsDiscreteValuationRing ↥W := by
  -- proof
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  let P : LaurentSeries L := hat (L := L) (PowerSeries.C ϖ)
  have hP0 : P ≠ 0 := hatC_ne_zero ϖ hϖ
  have hGP : G A P := G_hatC ϖ
  have hWG : ∀ f : E, f ∈ W ↔ G A (ι f) := fun f => hW f
  have hι0 : ∀ f : E, f ≠ 0 → ι f ≠ 0 := fun f hf => (map_ne_zero_iff ι ι.injective).mpr hf
  have hdec : ∀ f : E, f ∈ W → f ≠ 0 → ∃ (k : ℕ) (u : LaurentSeries L), GU A u ∧ ι f = P ^ k * u :=
    fun f hf hf0 => exists_eq_pow_mul_GU ϖ hϖ ((hWG f).mp hf) (hι0 f hf0)
  have hGUne : ∀ f : E, f ≠ 0 → ∀ (k : ℕ) (u : LaurentSeries L), ι f = P ^ k * u → u ≠ 0 := by
    intro f hf k u h hu
    apply hι0 f hf
    rw [h, hu, mul_zero]
  have hunit : ∀ (f : E) (hf : f ∈ W), f ≠ 0 → (IsUnit (⟨f, hf⟩ : ↥W) ↔ GU A (ι f)) := by
    intro f hf hf0
    constructor
    ·
      intro hu
      obtain ⟨v, hv⟩ := hu.exists_right_inv
      have hv' : f * (v : E) = 1 := congrArg Subtype.val hv
      have hvinv : (v : E) = f⁻¹ := eq_inv_of_mul_eq_one_right hv'
      refine ⟨(hWG f).mp hf, ?_⟩
      rw [← map_inv₀, ← hvinv]
      refine (hWG _).mp v.2
    ·
      intro hGU
      have hinv : f⁻¹ ∈ W := by
        refine (hWG _).mpr ?_
        rw [map_inv₀]
        refine hGU.2
      refine ⟨⟨⟨f, hf⟩, ⟨f⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hf0), Subtype.ext (inv_mul_cancel₀ hf0)⟩, rfl⟩
  obtain ⟨g, hgW⟩ : ∃ g : E, g ∉ W := by
    by_contra h
    push Not at h
    refine hne (eq_top_iff.mpr fun x _ => h x)
  have hg0 : g ≠ 0 := by
    intro hg
    subst hg
    refine hgW W.zero_mem
  have hginv : g⁻¹ ∈ W := (W.mem_or_inv_mem g).resolve_left hgW
  let S : ℕ → Prop := fun m => 0 < m ∧ ∃ f : E, f ∈ W ∧ f ≠ 0 ∧ ∃ u : LaurentSeries L, GU A u ∧ ι f = P ^ m * u
  have hS : ∃ m, S m := by
    obtain ⟨k, u, hu, hk⟩ := hdec g⁻¹ hginv (inv_ne_zero hg0)
    refine ⟨k, Nat.pos_of_ne_zero fun hk0 => ?_, g⁻¹, hginv, inv_ne_zero hg0, u, hu, hk⟩
    apply hgW
    rw [hk0, pow_zero, one_mul, map_inv₀] at hk
    refine (hWG g).mpr ?_
    have : ι g = u⁻¹ := by
      rw [← inv_inv (ι g), hk]
    rw [this]
    refine hu.2
  let d := Nat.find hS
  obtain ⟨hd0, p, hpW, hp0, up, hup, hpe⟩ : S d := Nat.find_spec hS
  have hdmin : ∀ m, S m → d ≤ m := fun m hm => Nat.find_min' hS hm
  have hup0 : up ≠ 0 := hGUne p hp0 d up hpe
  let pW : ↥W := ⟨p, hpW⟩
  have hfac : ∀ w : ↥W, w ≠ 0 → ∃ (n : ℕ) (v : ↥W), IsUnit v ∧ w = pW ^ n * v := by
    intro w hw
    have hw0 : (w : E) ≠ 0 := fun h => hw (Subtype.ext h)
    obtain ⟨k, u, hu, hk⟩ := hdec w w.2 hw0
    have hu0 : u ≠ 0 := hGUne w hw0 k u hk
    have hkd : k = d * (k / d) + k % d := (Nat.div_add_mod k d).symm
    have hpn0 : (p : E) ^ (k / d) ≠ 0 := pow_ne_zero _ hp0
    let z : E := (w : E) / p ^ (k / d)
    have hz : ι z = P ^ (k % d) * (u * (up ^ (k / d))⁻¹) := by
      show ι ((w : E) / p ^ (k / d)) = _
      rw [map_div₀, map_pow, hk, hpe, div_eq_iff (pow_ne_zero _ (by simpa [← hpe] using hι0 p hp0)), mul_pow, ← pow_mul]
      conv_lhs =>
        rw [hkd, pow_add]
      field_simp
    have hzGU : GU A (u * (up ^ (k / d))⁻¹) := GU_mul hu (GU_inv (GU_pow hup _))
    have hzW : z ∈ W := by
      refine (hWG z).mpr ?_
      rw [hz]
      refine G_mul (G_hatC_pow ϖ _) hzGU.1
    have hz0 : z ≠ 0 := div_ne_zero hw0 hpn0
    have hr0 : k % d = 0 := by
      by_contra hr
      have : S (k % d) := ⟨Nat.pos_of_ne_zero hr, z, hzW, hz0, _, hzGU, hz⟩
      refine absurd (hdmin _ this) (not_le.mpr (Nat.mod_lt k hd0))
    have hzunit : IsUnit (⟨z, hzW⟩ : ↥W) := by
      refine (hunit z hzW hz0).mpr ?_
      rw [hz, hr0, pow_zero, one_mul]
      refine hzGU
    refine ⟨k / d, ⟨z, hzW⟩, hzunit, Subtype.ext ?_⟩
    show (w : E) = p ^ (k / d) * ((w : E) / p ^ (k / d))
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hpn0]
  have hpW0 : pW ≠ 0 := fun h => hp0 (congrArg Subtype.val h)
  have hpirr : Irreducible pW := by
    refine ⟨fun hu => ?_, fun a b hab => ?_⟩
    ·
      have h1 : GU A (ι p) := (hunit p hpW hp0).mp hu
      have heq : P ^ d * up = P ^ 0 * ι p := by
        rw [pow_zero, one_mul]
        refine hpe.symm
      have := pow_mul_GU_inj (L := L) ϖ hϖ (k := d) (k' := 0) (u := up) (u' := ι p) hup h1 heq hup0
      omega
    ·
      have hab' : (p : E) = (a : E) * (b : E) := congrArg Subtype.val hab
      have ha0 : (a : E) ≠ 0 := fun h => hp0 (by rw [hab', h, zero_mul])
      have hb0 : (b : E) ≠ 0 := fun h => hp0 (by rw [hab', h, mul_zero])
      obtain ⟨ka, ua, hua, hka⟩ := hdec a a.2 ha0
      obtain ⟨kb, ub, hub, hkb⟩ := hdec b b.2 hb0
      have hsum : d = ka + kb := by
        apply pow_mul_GU_inj (L := L) ϖ hϖ hup (GU_mul hua hub) _ hup0
        rw [← hpe, hab', map_mul, hka, hkb, pow_add]
        ring
      if hka0 : ka = 0 then
        left
        rw [show a = ⟨(a : E), a.2⟩ from rfl]
        refine (hunit a a.2 ha0).mpr ?_
        rw [hka, hka0, pow_zero, one_mul]
        refine hua
      else
        if hkb0 : kb = 0 then
          right
          rw [show b = ⟨(b : E), b.2⟩ from rfl]
          refine (hunit b b.2 hb0).mpr ?_
          rw [hkb, hkb0, pow_zero, one_mul]
          refine hub
        else
          exfalso
          have : S ka := ⟨Nat.pos_of_ne_zero hka0, a, a.2, ha0, ua, hua, hka⟩
          have := hdmin _ this
          omega
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨pW, hpirr, fun {x} hx => ?_⟩
  obtain ⟨n, v, hv, hxv⟩ := hfac x hx
  refine ⟨n, hv.unit, by rw [IsUnit.unit_spec, hxv]⟩


-- created on 2026-10-21

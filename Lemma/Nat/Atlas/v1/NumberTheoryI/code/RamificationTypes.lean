import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.NumberTheoryI.code.RamificationTypes.Part2
open Ideal IsLocalRing


/--
[tamelyRamified_of_tower_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RamificationTypes.lean)
-/
@[path]
lemma tamelyRamified_of_tower_left
  {p e_EK e_EL e_LK : ℕ}
-- given
  (hmul : e_EK = e_EL * e_LK)
  (h : ¬ (p ∣ e_EK)) :
-- imply
  ¬ (p ∣ e_LK) :=
-- proof
  fun hd => h (hmul ▸ dvd_mul_of_dvd_right hd e_EL)

/--
[tamelyRamified_of_tower_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RamificationTypes.lean)
-/
@[path]
lemma tamelyRamified_of_tower_right
  {p e_EK e_EL e_LK : ℕ}
-- given
  (hmul : e_EK = e_EL * e_LK)
  (h : ¬ (p ∣ e_EK)) :
-- imply
  ¬ (p ∣ e_EL) :=
-- proof
  fun hd => h (hmul ▸ dvd_mul_of_dvd_left hd e_LK)

/--
[tamelyRamified_tower](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RamificationTypes.lean)
-/
@[path]
lemma tamelyRamified_tower
  {p e_EK e_EL e_LK : ℕ}
-- given
  (hp : Nat.Prime p ∨ p = 0)
  (hmul : e_EK = e_EL * e_LK)
  (hEL : ¬ (p ∣ e_EL))
  (hLK : ¬ (p ∣ e_LK)) :
-- imply
  ¬ (p ∣ e_EK) := by
-- proof
  rw [hmul]
  obtain hp | rfl := hp
  · exact hp.not_dvd_mul hEL hLK
  · simp only [zero_dvd_iff, mul_eq_zero, not_or] at *
    exact ⟨hEL, hLK⟩

/--
[tamelyRamified_tower_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RamificationTypes.lean)
-/
@[path]
lemma tamelyRamified_tower_iff
  {p e_EK e_EL e_LK : ℕ}
-- given
  (hp : Nat.Prime p ∨ p = 0)
  (hmul : e_EK = e_EL * e_LK) :
-- imply
  ¬ (p ∣ e_EK) ↔ ¬ (p ∣ e_EL) ∧ ¬ (p ∣ e_LK) :=
-- proof
  ⟨fun h => ⟨tamelyRamified_of_tower_right hmul h, tamelyRamified_of_tower_left hmul h⟩,
    fun ⟨hEL, hLK⟩ => tamelyRamified_tower hp hmul hEL hLK⟩

/--
[residueChar_prime_or_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RamificationTypes.lean)
-/
@[path]
lemma residueChar_prime_or_zero
  {p e_EK e_EL e_LK : ℕ}
  {F : Type*}
  [Field F] :
-- imply
  Nat.Prime (ringChar F) ∨ ringChar F = 0 := by
-- proof
  haveI := ringChar.charP F
  exact CharP.char_is_prime_or_zero F (ringChar F)
variable {f_EK f_EL f_LK : ℕ}

/--
[totallyRamified_tower](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RamificationTypes.lean)
-/
@[path]
lemma totallyRamified_tower
  {p e_EK e_EL e_LK : ℕ}
  {f_EK f_EL f_LK : ℕ}
-- given
  (hmul_f : f_EK = f_EL * f_LK)
  (hEL : f_EL = 1)
  (hLK : f_LK = 1) :
-- imply
  f_EK = 1 := by
-- proof
  rw [hmul_f, hEL, hLK, mul_one]
section TotallyTamelyRamifiedCharacterization
variable
  (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra B L] [IsFractionRing B L]
  [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]

/--
[nth_root_of_uniformizer_generates](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RamificationTypes.lean)
-/
@[path]
lemma nth_root_of_uniformizer_generates
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A L]
  [IsScalarTower A B L]
  [IsScalarTower A K L]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
  {n : ℕ}
  {π : B}
  {πA : A}
-- given
  (hn : 1 < n)
  (hπA : Irreducible πA)
  (hpow : π ^ n = algebraMap A B πA)
  (hn_eq : n = Module.finrank K L) :
-- imply
  Irreducible π ∧ Algebra.adjoin A ({π} : Set B) = ⊤ := by
-- proof
  obtain ⟨πB, hπB⟩ := IsDiscreteValuationRing.exists_irreducible (R := B)
  have hπ_ne_zero : π ≠ 0 := by
    intro h; rw [h, zero_pow (by omega : n ≠ 0)] at hpow
    exact hπA.ne_zero (FaithfulSMul.algebraMap_injective A B (hpow.symm.trans (map_zero _).symm))
  have hπ_not_unit : ¬IsUnit π := by
    intro h; have := h.pow n; rw [hpow] at this
    exact hπA.1 ((isUnit_map_iff (algebraMap A B) _).mp this)
  have hπ_span_ne_bot : Ideal.span {π} ≠ ⊥ := by
    rwa [ne_eq, Ideal.span_singleton_eq_bot]
  obtain ⟨k, hk_eq⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hπ_span_ne_bot hπB
  have h_maxB : IsLocalRing.maximalIdeal B = Ideal.span {πB} := hπB.maximalIdeal_eq
  have hk_max : Ideal.span {π} = (IsLocalRing.maximalIdeal B) ^ k := by
    rw [hk_eq, ← Ideal.span_singleton_pow, h_maxB]
  have hk_pos : 0 < k := by
    by_contra h; push Not at h; interval_cases k
    rw [pow_zero, Ideal.one_eq_top] at hk_max
    exact hπ_not_unit (Ideal.span_singleton_eq_top.mp hk_max)
  have hπA_span : IsLocalRing.maximalIdeal A = Ideal.span {πA} := hπA.maximalIdeal_eq
  have h_map : Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) =
    Ideal.span {algebraMap A B πA} := by
    rw [hπA_span, Ideal.map_span, Set.image_singleton]
  have h_span_pow : Ideal.span {algebraMap A B πA} = (Ideal.span {π}) ^ n := by
    rw [Ideal.span_singleton_pow, ← hpow]
  have h_map_eq : Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) =
    (IsLocalRing.maximalIdeal B) ^ (n * k) := by
    rw [h_map, h_span_pow, hk_max, ← pow_mul, mul_comm]
  have h_degree := AKLB_degree_eq_ramIdx_mul_resDeg A K B L
  have hπA_B_ne_zero : algebraMap A B πA ≠ 0 := by
    intro h
    exact hπA.ne_zero (FaithfulSMul.algebraMap_injective A B (h.trans (map_zero _).symm))
  have hnk_ne : n * k ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  have h_map_ne_bot : Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) ≠ ⊥ := by
    rw [h_map_eq]; exact (pow_ne_zero_iff hnk_ne).mpr
      (IsDiscreteValuationRing.not_a_field B)
  have hPbot : IsLocalRing.maximalIdeal B ≠ ⊥ := IsDiscreteValuationRing.not_a_field B
  have hPprime : (IsLocalRing.maximalIdeal B).IsPrime := Ideal.IsMaximal.isPrime
    (IsLocalRing.maximalIdeal.isMaximal (R := B))
  have he_eq_nk : (IsLocalRing.maximalIdeal A).ramificationIdx (IsLocalRing.maximalIdeal B) =
    n * k := by
    rw [Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count h_map_ne_bot
      hPprime hPbot, h_map_eq, UniqueFactorizationMonoid.normalizedFactors_pow,
      Multiset.count_nsmul,
      UniqueFactorizationMonoid.normalizedFactors_irreducible
        (Ideal.prime_of_isPrime hPbot hPprime).irreducible]
    simp [normalize_eq]
  have he_pos : 0 < (IsLocalRing.maximalIdeal A).ramificationIdx (IsLocalRing.maximalIdeal B) := by
    rw [he_eq_nk]; exact Nat.mul_pos (by omega) hk_pos
  have h_fk_eq_1 : AKLB_resDeg A B * k = 1 := by
    have h_n_eq_ef : n = (IsLocalRing.maximalIdeal A).ramificationIdx (IsLocalRing.maximalIdeal B)
      * AKLB_resDeg A B := by rw [hn_eq]; exact h_degree
    nlinarith [he_eq_nk]
  have hk_eq_1 : k = 1 := Nat.eq_one_of_mul_eq_one_left h_fk_eq_1
  have hf_eq_1 : AKLB_resDeg A B = 1 := Nat.eq_one_of_mul_eq_one_right h_fk_eq_1
  have h_span_eq : Ideal.span {π} = IsLocalRing.maximalIdeal B := by
    rw [hk_max, hk_eq_1, pow_one]
  have hπ_irr : Irreducible π :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr h_span_eq.symm
  have htotram : (IsLocalRing.maximalIdeal A).ramificationIdx (IsLocalRing.maximalIdeal B) =
    Module.finrank K L := by
    rw [he_eq_nk, hk_eq_1, mul_one, hn_eq]
  constructor
  · exact hπ_irr
  · exact totally_ramified_adjoin_uniformizer A K B L π hπ_irr htotram

/--
[uniformizer_pow_associated_algebraMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RamificationTypes.lean)
-/
@[path]
lemma uniformizer_pow_associated_algebraMap
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A L]
  [IsScalarTower A B L]
  [IsScalarTower A K L]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
  {πA₀ : A}
  {πB : B}
-- given
  (htotram : AKLB_ramIdx A B = Module.finrank K L)
  (hπA₀ : Irreducible πA₀)
  (hπB : Irreducible πB) :
-- imply
  ∃ u : Bˣ, πB ^ (Module.finrank K L) = ↑u * algebraMap A B πA₀ := by
-- proof
  have hne : algebraMap A B πA₀ ≠ 0 := by
    simp only [ne_eq, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective A B)]
    exact hπA₀.ne_zero
  obtain ⟨m, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hπB
  have hram : (maximalIdeal A).ramificationIdx (maximalIdeal B) = m := by
    have hmap : Ideal.map (algebraMap A B) (maximalIdeal A) = (maximalIdeal B) ^ m := by
      rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer πA₀).mp hπA₀,
        Ideal.map_span, Set.image_singleton, hv]
      rw [show (↑v : B) * πB ^ m = πB ^ m * ↑v from mul_comm _ _,
        ← Ideal.span_singleton_mul_span_singleton]
      simp [Ideal.span_singleton_eq_top.mpr (Units.isUnit v),
        ← Ideal.span_singleton_pow,
        ← (IsDiscreteValuationRing.irreducible_iff_uniformizer πB).mp hπB]
    have hmap_ne : Ideal.map (algebraMap A B) (maximalIdeal A) ≠ ⊥ := by
      rw [hmap, (IsDiscreteValuationRing.irreducible_iff_uniformizer πB).mp hπB,
        Ideal.span_singleton_pow, ne_eq, Ideal.span_singleton_eq_bot]
      exact pow_ne_zero _ hπB.ne_zero
    rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity hmap_ne
      (Ideal.IsMaximal.isPrime' (maximalIdeal B)),
      hmap]
    apply multiplicity_pow_self
    · rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer πB).mp hπB,
      ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact hπB.ne_zero
    · rw [Ideal.isUnit_iff]
      exact (IsLocalRing.maximalIdeal.isMaximal (R := B)).ne_top
  have hm : m = Module.finrank K L := by
    rw [← htotram]; exact hram.symm
  refine ⟨v⁻¹, ?_⟩
  rw [hm] at hv
  rw [hv, ← mul_assoc]
  simp

/--
[hensel_unit_nth_root_of_one_mod](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RamificationTypes.lean)
-/
@[path]
lemma hensel_unit_nth_root_of_one_mod
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
  {n : ℕ}
  {u : Bˣ}
-- given
  (hn : 1 < n)
  (hp : ¬ (ringChar (IsLocalRing.ResidueField B) ∣ n))
  (hu_mod : (u : B) - 1 ∈ IsLocalRing.maximalIdeal B) :
-- imply
  ∃ r : Bˣ, (↑r : B) ^ n = ↑u := by
-- proof
  open Polynomial IsLocalRing in
  haveI : HenselianRing B (maximalIdeal B) := inferInstance
  set f := X ^ n - C (u : B)
  have hf_monic : f.Monic := monic_X_pow_sub_C _ (by omega)
  have hf_eval : f.eval 1 ∈ maximalIdeal B := by
    simp only [f, eval_sub, eval_pow, eval_X, eval_C, one_pow]
    rw [show (1 : B) - ↑u = -(↑u - 1) from by ring]
    exact (maximalIdeal B).neg_mem hu_mod
  have hf_deriv : IsUnit (Ideal.Quotient.mk (maximalIdeal B) (f.derivative.eval 1)) := by
    simp only [f, derivative_sub, derivative_C, sub_zero, derivative_pow, derivative_X, mul_one,
      eval_mul, eval_pow, eval_X, one_pow, mul_one, map_natCast, eval_natCast]
    change IsUnit ((n : ResidueField B))
    rw [isUnit_iff_ne_zero]; exact fun h => hp (ringChar.dvd h)
  obtain ⟨a, ha_root, ha_close⟩ := HenselianRing.is_henselian f hf_monic 1 hf_eval hf_deriv
  have ha_pow : a ^ n = (u : B) := by
    have h : f.eval a = 0 := ha_root
    simp only [f, eval_sub, eval_pow, eval_X, eval_C] at h
    exact sub_eq_zero.mp h
  have ha_unit : IsUnit a := by
    by_contra ha_nmem
    have ha_mem : a ∈ maximalIdeal B := ha_nmem
    have h1_mem : (1 : B) ∈ maximalIdeal B := by
      have : (1 : B) = a - (a - 1) := by ring
      rw [this]; exact Ideal.sub_mem _ ha_mem ha_close
    have := (maximalIdeal.isMaximal B).ne_top
    rw [Ideal.ne_top_iff_one] at this; exact this h1_mem
  obtain ⟨r, rfl⟩ := ha_unit
  exact ⟨r, ha_pow⟩

/--
[uniformizer_adjust_mod_maximal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RamificationTypes.lean)
-/
@[path]
lemma uniformizer_adjust_mod_maximal
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A L]
  [IsScalarTower A B L]
  [IsScalarTower A K L]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
  {πA₀ : A}
  {πB : B}
  {u : Bˣ}
-- given
  (htotram : AKLB_ramIdx A B = Module.finrank K L)
  (hπA₀ : Irreducible πA₀)
  (hπB : Irreducible πB)
  (hu : πB ^ (Module.finrank K L) = ↑u * algebraMap A B πA₀) :
-- imply
  ∃ (πA₁ : A) (u₁ : Bˣ), Irreducible πA₁ ∧ πB ^ (Module.finrank K L) = ↑u₁ * algebraMap A B πA₁ ∧ ((u₁ : B) - 1) ∈ IsLocalRing.maximalIdeal B := by
-- proof
  have hfund := AKLB_degree_eq_ramIdx_mul_resDeg A K B L
  have hn_pos : 0 < Module.finrank K L := Module.finrank_pos
  have hf1 : AKLB_resDeg A B = 1 := by
    rw [htotram] at hfund; nlinarith
  have hsurj : Function.Surjective
    (algebraMap (ResidueField A) (ResidueField B)) := by
    haveI : FiniteDimensional (ResidueField A) (ResidueField B) :=
      FiniteDimensional.of_finrank_pos (by change 0 < AKLB_resDeg A B; omega)
    have hrange : (Algebra.linearMap (ResidueField A) (ResidueField B)).range = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [LinearMap.finrank_range_of_inj
        (algebraMap (ResidueField A) (ResidueField B)).injective,
        Module.finrank_self]; exact hf1.symm
    rwa [LinearMap.range_eq_top] at hrange
  obtain ⟨abar, habar⟩ := hsurj ((residue B) (u : B))
  obtain ⟨a, ha⟩ := residue_surjective (R := A) abar
  have hres_eq : (residue B) ((algebraMap A B) a) = (residue B) (u : B) := by
    have h1 := RingHom.congr_fun (ResidueField.map_comp_residue (algebraMap A B)) a
    simp only [RingHom.comp_apply] at h1
    rw [← h1, ha]; exact habar
  have ha_unit : IsUnit a := by
    by_contra h_nonunit
    have ha_mem : a ∈ maximalIdeal A := by rwa [mem_maximalIdeal]
    have hab_mem : (algebraMap A B) a ∈ maximalIdeal B :=
      map_nonunit (algebraMap A B) a ha_mem
    rw [← residue_eq_zero_iff] at hab_mem
    rw [hres_eq] at hab_mem
    exact (RingHom.isUnit_map _ u.isUnit).ne_zero hab_mem
  obtain ⟨aA, haA⟩ := ha_unit
  set bA := Units.map (algebraMap A B).toMonoidHom aA with hbA_def
  refine ⟨(aA : A) * πA₀, u * bA⁻¹, ?_, ?_, ?_⟩
  ·
    exact (associated_unit_mul_right πA₀ aA aA.isUnit).irreducible hπA₀
  ·
    rw [Units.val_mul, map_mul]
    have hbA_inv_val : (↑bA⁻¹ : B) = algebraMap A B (↑aA⁻¹ : A) := by simp [bA]
    have h_cancel : (algebraMap A B) (↑aA⁻¹ : A) * (algebraMap A B) (↑aA : A) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    rw [show ↑u * ↑bA⁻¹ * ((algebraMap A B) ↑aA * (algebraMap A B) πA₀) =
      ↑u * (↑bA⁻¹ * (algebraMap A B) ↑aA) * (algebraMap A B) πA₀ from by ring]
    rwa [hbA_inv_val, h_cancel, mul_one]
  ·
    rw [← residue_eq_zero_iff, map_sub, map_one, sub_eq_zero]
    show (residue B) (↑(u * bA⁻¹)) = 1
    rw [Units.val_mul, map_mul]
    have hbA_val : (↑bA : B) = algebraMap A B (↑aA : A) := by simp [bA]
    rw [← haA] at hres_eq
    rw [← hbA_val] at hres_eq
    rw [← hres_eq, ← map_mul, Units.mul_inv, map_one]

/--
[isPrecomplete_of_pow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RamificationTypes.lean)
-/
@[path]
lemma isPrecomplete_of_pow
  [CommRing R]
  {I : Ideal R}
  [AddCommGroup M]
  [Module R M]
  {e : ℕ}
  [hpc : IsPrecomplete (I ^ e) M]
-- given
  (he : 1 ≤ e) :
-- imply
  IsPrecomplete I M := by
-- proof
  constructor
  intro f hf
  have hcauchy : ∀ {m n : ℕ}, m ≤ n →
    f (m * e) ≡ f (n * e) [SMOD (I ^ e) ^ m • (⊤ : Submodule R M)] := by
    intro m n hmn
    rw [show (I ^ e) ^ m = I ^ (m * e) from by rw [← pow_mul, mul_comm]]
    exact hf (Nat.mul_le_mul_right e hmn)
  obtain ⟨L, hL⟩ := hpc.prec' (fun n => f (n * e)) hcauchy
  exact ⟨L, fun n => by
    have h1 : f n ≡ f (n * e) [SMOD I ^ n • (⊤ : Submodule R M)] :=
      hf (Nat.le_mul_of_pos_right n (by omega))
    have h2 : f (n * e) ≡ L [SMOD (I ^ e) ^ n • (⊤ : Submodule R M)] := hL n
    rw [show (I ^ e) ^ n = I ^ (n * e) from by rw [← pow_mul, mul_comm]] at h2
    exact h1.trans (SModEq.mono (Submodule.smul_mono_left
      (Ideal.pow_le_pow_right (Nat.le_mul_of_pos_right n (by omega)))) h2)⟩
set_option maxHeartbeats 400000 in

/--
[finite_extension_adic_complete](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RamificationTypes.lean)
-/
@[path]
lemma finite_extension_adic_complete
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  [NoZeroSMulDivisors A B] :
-- imply
  IsAdicComplete (IsLocalRing.maximalIdeal B) B := by
-- proof
  rw [isAdicComplete_iff]
  refine ⟨inferInstance, ?_⟩
  have hpc_A : IsPrecomplete (IsLocalRing.maximalIdeal A) B := by
    rw [← AdicCompletion.of_surjective_iff]
    set I := IsLocalRing.maximalIdeal A
    have hsurj_tp := AdicCompletion.ofTensorProduct_surjective_of_finite I B
    have hsurj_A : Function.Surjective (AdicCompletion.of I A) :=
      (AdicCompletion.of_bijective_iff.mpr inferInstance).2
    suffices h : ∀ t, AdicCompletion.ofTensorProduct I B t ∈
      LinearMap.range (AdicCompletion.of I B) by
      intro y
      obtain ⟨t, ht⟩ := hsurj_tp y
      exact ⟨(h t).choose, by rw [(h t).choose_spec, ht]⟩
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul r b =>
      obtain ⟨a, ha⟩ := hsurj_A r
      exact ⟨a • b, by
        rw [AdicCompletion.ofTensorProduct_tmul, ← ha, map_smul]; rfl⟩
    | add x y hx hy =>
      obtain ⟨bx, hbx⟩ := hx
      obtain ⟨by_, hby⟩ := hy
      exact ⟨bx + by_, by simp [map_add, hbx, hby]⟩
  have hpc_map : IsPrecomplete (Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)) B :=
    IsPrecomplete.map_algebraMap_iff.mpr hpc_A
  set J := Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) with hJ_def
  have hle : J ≤ IsLocalRing.maximalIdeal B := by
    rw [Ideal.map_le_iff_le_comap, IsLocalRing.maximalIdeal_comap]
  have hJne : J ≠ ⊥ := by
    intro h
    rw [hJ_def, Ideal.map_eq_bot_iff_le_ker] at h
    have hker : RingHom.ker (algebraMap A B) = ⊥ :=
      (RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective A B)
    rw [hker] at h
    exact IsDiscreteValuationRing.not_a_field A (le_bot_iff.mp h)
  obtain ⟨e, he⟩ := exists_maximalIdeal_pow_eq_of_principal B
    (IsPrincipalIdealRing.principal _) J hJne
  have he1 : 1 ≤ e := by
    by_contra h
    push Not at h
    interval_cases e
    simp only [pow_zero, Ideal.one_eq_top] at he
    exact (IsLocalRing.maximalIdeal.isMaximal (R := B)).ne_top
      (eq_top_iff.mpr (he ▸ hle))
  rw [he] at hpc_map
  exact isPrecomplete_of_pow e he1 (hpc := hpc_map)

/--
[residue_char_eq_of_local_hom](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RamificationTypes.lean)
-/
@[path]
lemma residue_char_eq_of_local_hom
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)] :
-- imply
  ringChar (IsLocalRing.ResidueField B) = ringChar (IsLocalRing.ResidueField A) := by
-- proof
  letI : Algebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) :=
    (IsLocalRing.ResidueField.map (algebraMap A B)).toAlgebra
  exact (Algebra.ringChar_eq (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)).symm

/--
[totally_tamely_ramified_has_nth_root](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RamificationTypes.lean)
-/
@[path]
lemma totally_tamely_ramified_has_nth_root
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A L]
  [IsScalarTower A B L]
  [IsScalarTower A K L]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
-- given
  (htotram : AKLB_ramIdx A B = Module.finrank K L)
  (htame : ¬ (AKLB_residueChar A ∣ AKLB_ramIdx A B))
  (hn1 : 1 < Module.finrank K L) :
-- imply
  ∃ (πA : A) (π : B), Irreducible πA ∧ π ^ (Module.finrank K L) = algebraMap A B πA ∧ Algebra.adjoin A ({π} : Set B) = ⊤ := by
-- proof
  set n := Module.finrank K L with hn_def
  have key : ∃ (πA₀ : A) (πB : B) (u : Bˣ) (r : Bˣ),
    Irreducible πA₀ ∧ 1 < n ∧ πB ^ n = ↑u * algebraMap A B πA₀ ∧ (↑r : B) ^ n = ↑u := by
    obtain ⟨πA₀, hπA₀⟩ := IsDiscreteValuationRing.exists_irreducible A
    obtain ⟨πB, hπB⟩ := IsDiscreteValuationRing.exists_irreducible B
    obtain ⟨u₀, hu₀⟩ := uniformizer_pow_associated_algebraMap A K B L htotram πA₀ hπA₀ πB hπB
    obtain ⟨πA₁, u₁, hπA₁, hu₁, hu₁_mod⟩ :=
      uniformizer_adjust_mod_maximal A K B L htotram πA₀ hπA₀ πB hπB u₀ hu₀
    haveI : IsAdicComplete (IsLocalRing.maximalIdeal B) B :=
      finite_extension_adic_complete A B
    have hchar : ringChar (IsLocalRing.ResidueField B) = ringChar (IsLocalRing.ResidueField A) :=
      residue_char_eq_of_local_hom A B
    have htame_B : ¬ (ringChar (IsLocalRing.ResidueField B) ∣ n) := by
      rw [hchar]; rwa [htotram] at htame
    obtain ⟨r, hr⟩ := hensel_unit_nth_root_of_one_mod B n hn1 htame_B u₁ hu₁_mod
    exact ⟨πA₁, πB, u₁, r, hπA₁, hn1, hu₁, hr⟩
  obtain ⟨πA₀, πB, u, r, hπA₀, hn1, hu, hr⟩ := key
  refine ⟨πA₀, πB * ↑(r⁻¹ : Bˣ), hπA₀, ?_, ?_⟩
  ·
    have hrinv_pow : (r⁻¹ : Bˣ) ^ n = u⁻¹ := by
      rw [inv_pow]; congr 1; ext; exact hr
    rw [mul_pow, hu, ← Units.val_pow_eq_pow_val, hrinv_pow]
    rw [mul_assoc, mul_comm (algebraMap A B πA₀) (↑(u⁻¹ : Bˣ)), ← mul_assoc]
    simp [Units.mul_inv]
  ·
    have hpow : (πB * ↑(r⁻¹ : Bˣ)) ^ n = algebraMap A B πA₀ := by
      have hrinv_pow : (r⁻¹ : Bˣ) ^ n = u⁻¹ := by
        rw [inv_pow]; congr 1; ext; exact hr
      rw [mul_pow, hu, ← Units.val_pow_eq_pow_val, hrinv_pow]
      rw [mul_assoc, mul_comm (algebraMap A B πA₀) (↑(u⁻¹ : Bˣ)), ← mul_assoc]
      simp [Units.mul_inv]
    have := nth_root_of_uniformizer_generates A K B L n hn1
      (πB * ↑(r⁻¹ : Bˣ)) πA₀ hπA₀ hpow rfl
    exact this.2

/--
[totallyTamelyRamified_of_nthRootOfUniformizer](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RamificationTypes.lean)
-/
@[path]
lemma totallyTamelyRamified_of_nthRootOfUniformizer
  {π : B}
  {πA : A}
-- given
  (hn : 1 < Module.finrank K L)
  (hroot : IsNthRootOfUniformizer A B (Module.finrank K L) π πA)
  (htame : ¬ (AKLB_residueChar A ∣ Module.finrank K L)) :
-- imply
  AKLB_IsTotallyTamelyRamified A K B L := by
-- proof
  have ⟨hπ_irr, hadj⟩ :=
    nth_root_of_uniformizer_generates A K B L (Module.finrank K L) hn π πA
      hroot.uniformizer_A hroot.pow_eq rfl
  have hsurj : Function.Surjective (IsLocalRing.ResidueField.map (algebraMap A B)) :=
    residueField_map_surj_of_adjoin_uniformizer π hπ_irr hadj
  have hf1 : AKLB_resDeg A B = 1 :=
    finrank_eq_one_of_algebraMap_surjective hsurj
  have hfund := AKLB_degree_eq_ramIdx_mul_resDeg A K B L
  rw [hf1, mul_one] at hfund
  exact ⟨hfund.symm, hfund.symm ▸ htame, hn⟩

/--
[nthRootOfUniformizer_of_totallyTamelyRamified](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RamificationTypes.lean)
-/
@[path]
lemma nthRootOfUniformizer_of_totallyTamelyRamified
-- given
  (httr : AKLB_IsTotallyTamelyRamified A K B L) :
-- imply
  ∃ (πA : A) (π : B), IsNthRootOfUniformizer A B (Module.finrank K L) π πA := by
-- proof
  obtain ⟨htotram, htame, hlt⟩ := httr
  obtain ⟨πA, π, hπA, hpow, hadj⟩ :=
    totally_tamely_ramified_has_nth_root A K B L htotram htame hlt
  exact ⟨πA, π, hπA, hpow, hadj⟩

/--
[totallyTamelyRamified_iff_nthRootOfUniformizer](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RamificationTypes.lean)
-/
@[path]
lemma totallyTamelyRamified_iff_nthRootOfUniformizer
-- given
  (hn : 1 < Module.finrank K L)
  (htame_deg : ¬ (AKLB_residueChar A ∣ Module.finrank K L)) :
-- imply
  AKLB_IsTotallyTamelyRamified A K B L ↔ ∃ (πA : A) (π : B), IsNthRootOfUniformizer A B (Module.finrank K L) π πA := by
-- proof
  constructor
  · exact nthRootOfUniformizer_of_totallyTamelyRamified A K B L
  · rintro ⟨πA, π, hroot⟩
    exact totallyTamelyRamified_of_nthRootOfUniformizer A K B L hn π πA hroot htame_deg
end TotallyTamelyRamifiedCharacterization
section PadicDecompositionArithmetic

/--
[padic_decomp_exists](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RamificationTypes.lean)
-/
@[path]
lemma padic_decomp_exists
  {e : ℕ}
  {p : ℕ}
-- given
  (he : e ≠ 0)
  (hp : Nat.Prime p ∨ p = 0) :
-- imply
  ∃ m a, e = m * p ^ a ∧ ¬(p ∣ m) := by
-- proof
  obtain hp | rfl := hp
  · obtain ⟨a, m, hm, heq⟩ := Nat.exists_eq_pow_mul_and_not_dvd he p hp.one_lt.ne'
    exact ⟨m, a, by rw [heq, mul_comm], hm⟩
  · exact ⟨e, 0, by simp, by simp [he]⟩

/--
[padic_decomp_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RamificationTypes.lean)
-/
@[path]
lemma padic_decomp_unique
  {p : ℕ}
  {m₁ m₂ a₁ a₂ : ℕ}
-- given
  (hp : Nat.Prime p ∨ p = 0)
  (hm₁ : ¬(p ∣ m₁))
  (hm₂ : ¬(p ∣ m₂))
  (hne : m₁ * p ^ a₁ ≠ 0)
  (heq : m₁ * p ^ a₁ = m₂ * p ^ a₂) :
-- imply
  m₁ = m₂ ∧ a₁ = a₂ := by
-- proof
  obtain hp | rfl := hp
  ·
    suffices ha : a₁ = a₂ by
      subst ha
      exact ⟨Nat.eq_of_mul_eq_mul_right
        (Nat.pos_of_ne_zero (pow_ne_zero _ hp.ne_zero)) heq, rfl⟩
    by_contra hab
    have key : ∀ {m₁ m₂ a₁ a₂ : ℕ}, ¬(p ∣ m₁) →
      m₁ * p ^ a₁ = m₂ * p ^ a₂ → a₁ < a₂ → False := by
      intro m₁ m₂ a₁ a₂ hm heq h
      have heq' : m₁ * p ^ a₁ = m₂ * p ^ (a₂ - a₁) * p ^ a₁ := by
        rw [mul_assoc, ← pow_add, Nat.sub_add_cancel (le_of_lt h)]; exact heq
      have hm₁eq : m₁ = m₂ * p ^ (a₂ - a₁) :=
        Nat.eq_of_mul_eq_mul_right
          (Nat.pos_of_ne_zero (pow_ne_zero _ hp.ne_zero)) heq'
      exact hm (hm₁eq ▸ dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) m₂)
    obtain h | h := Nat.lt_or_gt_of_ne hab
    · exact key hm₁ heq h
    · exact key hm₂ heq.symm h
  ·
    simp only [zero_dvd_iff] at hm₁ hm₂
    obtain rfl | ha₁ := Nat.eq_zero_or_pos a₁
      obtain rfl | ha₂ := Nat.eq_zero_or_pos a₂
    · simp at heq; exact ⟨heq, rfl⟩
    · simp [zero_pow (by omega : a₂ ≠ 0)] at heq; omega
    · simp [zero_pow (by omega : a₁ ≠ 0)] at heq; omega
    · simp [zero_pow (by omega : a₁ ≠ 0)] at hne

/--
[padic_decomp_unique_tower](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RamificationTypes.lean)
-/
@[path]
lemma padic_decomp_unique_tower
  {p : ℕ}
  {e m₁ m₂ a₁ a₂ : ℕ}
-- given
  (hp : Nat.Prime p ∨ p = 0)
  (he : e ≠ 0)
  (heq₁ : e = m₁ * p ^ a₁)
  (hm₁ : ¬(p ∣ m₁))
  (heq₂ : e = m₂ * p ^ a₂)
  (hm₂ : ¬(p ∣ m₂)) :
-- imply
  m₁ = m₂ ∧ a₁ = a₂ :=
-- proof
  padic_decomp_unique p hp m₁ m₂ a₁ a₂ hm₁ hm₂ (heq₁ ▸ he) (by rw [← heq₂, ← heq₁])
end PadicDecompositionArithmetic
section TameWildDecompositionTotallyRamified

/--
[IntermediateField.adjoin_singleton_eq_of_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RamificationTypes.lean)
-/
@[path]
lemma IntermediateField.adjoin_singleton_eq_of_smul
  [Field K]
  [Field L]
  [Algebra K L]
  {α β : L}
-- given
  (h0 : ∃ k : K, algebraMap K L k * β = α)
  (h1 : ∃ k : K, algebraMap K L k * α = β) :
-- imply
  IntermediateField.adjoin K ({α} : Set L) = IntermediateField.adjoin K ({β} : Set L) := by
-- proof
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx
    obtain ⟨k, hk⟩ := h1; rw [← hk]
    exact mul_mem (IntermediateField.algebraMap_mem _ k)
      (IntermediateField.subset_adjoin K {β} rfl)
  · rw [IntermediateField.adjoin_le_iff]
    intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx
    obtain ⟨k, hk⟩ := h2; rw [← hk]
    exact mul_mem (IntermediateField.algebraMap_mem _ k)
      (IntermediateField.subset_adjoin K {α} rfl)

/--
[ratio_pow_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RamificationTypes.lean)
-/
@[path]
lemma ratio_pow_eq_one
  [Field L]
  {α β c : L}
  {m : ℕ}
-- given
  (hα : α ^ m = c)
  (hβ : β ^ m = c)
  (hc : c ≠ 0) :
-- imply
  (α * β⁻¹) ^ m = 1 := by
-- proof
  rw [mul_pow, hα, inv_pow, hβ, mul_inv_cancel₀ hc]

/--
[hensel_dvr_mth_root_of_uniformizer](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RamificationTypes.lean)
-/
@[path]
lemma hensel_dvr_mth_root_of_uniformizer
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A L]
  [IsScalarTower A B L]
  [IsScalarTower A K L]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
  {m : ℕ}
-- given
  (htotram : AKLB_ramIdx A B = Module.finrank K L)
  (hm : ¬ (AKLB_residueChar A ∣ m))
  (hm_dvd : m ∣ Module.finrank K L) :
-- imply
  ∃ (ϖ : A) (π : L), Irreducible ϖ ∧ π ^ m = algebraMap K L (algebraMap A K ϖ) ∧ π ≠ 0 := by
-- proof
  have hm_ne : m ≠ 0 := by
    intro h; subst h; exact hm (dvd_zero _)
  by_cases hm1 : m = 1
  · subst hm1
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
    refine ⟨ϖ, algebraMap K L (algebraMap A K ϖ), hϖ, pow_one _, ?_⟩
    simp only [ne_eq, map_eq_zero, map_eq_zero_iff _ (IsFractionRing.injective A K)]
    exact hϖ.ne_zero
  · have hm_ge2 : 1 < m := by omega
    obtain ⟨πA₀, hπA₀⟩ := IsDiscreteValuationRing.exists_irreducible A
    obtain ⟨πB, hπB_irr⟩ := IsDiscreteValuationRing.exists_irreducible B
    haveI hB_complete : IsAdicComplete (IsLocalRing.maximalIdeal B) B :=
      finite_extension_adic_complete A B
    obtain ⟨u₀, hu₀⟩ := uniformizer_pow_associated_algebraMap A K B L htotram πA₀ hπA₀ πB hπB_irr
    obtain ⟨ϖ, u₁, hϖ, hu₁, hu₁_mod⟩ :=
      uniformizer_adjust_mod_maximal A K B L htotram πA₀ hπA₀ πB hπB_irr u₀ hu₀
    have hm_B : ¬ (ringChar (IsLocalRing.ResidueField B) ∣ m) := by
      rwa [residue_char_eq_of_local_hom A B]
    obtain ⟨r, hr⟩ := hensel_unit_nth_root_of_one_mod B m hm_ge2 hm_B u₁ hu₁_mod
    set n := Module.finrank K L with hn_def
    obtain ⟨k, hk⟩ := hm_dvd
    set πB_L := algebraMap B L πB
    set r_L := algebraMap B L (↑r : B)
    have hr_L_ne : r_L ≠ 0 := by
      simp only [r_L, ne_eq, map_eq_zero_iff _ (IsFractionRing.injective B L)]
      exact Units.ne_zero r
    refine ⟨ϖ, πB_L ^ k / r_L, hϖ, ?_, ?_⟩
    ·
      rw [div_pow, ← pow_mul, mul_comm k m, ← hk]
      have h1 : πB_L ^ n = algebraMap B L (↑u₁ : B) * algebraMap B L (algebraMap A B ϖ) := by
        rw [← map_pow, hu₁, map_mul]
      have h2 : r_L ^ m = algebraMap B L (↑u₁ : B) := by
        rw [← map_pow, hr]
      have h3 : algebraMap B L (algebraMap A B ϖ) = algebraMap K L (algebraMap A K ϖ) := by
        rw [← IsScalarTower.algebraMap_apply A B L,
          ← IsScalarTower.algebraMap_apply A K L]
      rw [h2, h1, h3]
      have hu_L_ne : algebraMap B L (↑u₁ : B) ≠ 0 := by
        simp only [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective B L)]
        exact Units.ne_zero u₁
      field_simp
    ·
      apply div_ne_zero
      · apply pow_ne_zero
        show πB_L ≠ 0
        simp only [πB_L, ne_eq, map_eq_zero_iff _ (IsFractionRing.injective B L)]
        exact hπB_irr.ne_zero
      · exact hr_L_ne

/--
[hensel_uniformizer_construction](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RamificationTypes.lean)
-/
@[path]
lemma hensel_uniformizer_construction
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A L]
  [IsScalarTower A B L]
  [IsScalarTower A K L]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
  {m a : ℕ}
-- given
  (htotram : AKLB_ramIdx A B = Module.finrank K L)
  (hma : Module.finrank K L = m * (AKLB_residueChar A) ^ a)
  (hm : ¬ (AKLB_residueChar A ∣ m)) :
-- imply
  ∃ (πA_img : K) (π : L), π ^ m = algebraMap K L πA_img ∧ algebraMap K L πA_img ≠ 0 ∧ π ≠ 0 ∧ Module.finrank K (IntermediateField.adjoin K ({π} : Set L)) = m ∧ Module.finrank (IntermediateField.adjoin K ({π} : Set L)) L = (AKLB_residueChar A) ^ a ∧ (∃ πA : A, Irreducible πA ∧ algebraMap A K πA = πA_img) := by
-- proof
  have core : ∃ (πA_img : K) (π : L),
    π ^ m = algebraMap K L πA_img ∧
    algebraMap K L πA_img ≠ 0 ∧
    π ≠ 0 ∧
    Module.finrank K (IntermediateField.adjoin K ({π} : Set L)) = m ∧
    (∃ πA : A, Irreducible πA ∧ algebraMap A K πA = πA_img) := by
    obtain ⟨ϖ, π, hϖ_irr, hπ_pow, hπ_ne⟩ :=
      hensel_dvr_mth_root_of_uniformizer A K B L htotram m hm
        ⟨(AKLB_residueChar A) ^ a, hma⟩
    have hπA_img_ne : algebraMap K L (algebraMap A K ϖ) ≠ 0 := by
      simp only [ne_eq, map_eq_zero]
      rw [← map_zero (algebraMap A K)]
      exact (IsFractionRing.injective A K).ne hϖ_irr.ne_zero
    have step_iii : Module.finrank K (IntermediateField.adjoin K ({π} : Set L)) = m := by
      have hm_pos : 0 < m := by
        obtain rfl | h := Nat.eq_zero_or_pos m
        · simp only [zero_mul] at hma
          linarith [Module.finrank_pos (R := K) (M := L)]
        · exact h
      have hm_ne : m ≠ 0 := Nat.pos_iff_ne_zero.mp hm_pos
      open Polynomial in
      have heis : (X ^ m - C ϖ : Polynomial A).IsEisensteinAt
        (IsLocalRing.maximalIdeal A) := by
        apply (monic_X_pow_sub_C ϖ hm_ne).isEisensteinAt_of_mem_of_notMem
        · exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top
        · intro n hn
          rw [natDegree_X_pow_sub_C] at hn
          simp only [coeff_sub, coeff_X_pow, coeff_C,
            if_neg (Nat.ne_of_lt hn), zero_sub, neg_mem_iff]
          split_ifs with h0
          · subst h0; rw [IsLocalRing.mem_maximalIdeal]; exact hϖ_irr.1
          · exact (IsLocalRing.maximalIdeal A).zero_mem
        · simp only [coeff_sub, coeff_X_pow, coeff_C, eq_comm, hm_ne, if_false,
          if_true, zero_sub]
          rw [Ideal.neg_mem_iff, hϖ_irr.maximalIdeal_eq, Ideal.span_singleton_pow,
            Ideal.mem_span_singleton]
          intro ⟨a, ha⟩; rw [sq, mul_assoc] at ha
          exact hϖ_irr.1 (IsUnit.of_mul_eq_one a
            (mul_left_cancel₀ hϖ_irr.ne_zero (by rw [mul_one]; exact ha)).symm)
      open Polynomial in
      have hirr_A : Irreducible (X ^ m - C ϖ : Polynomial A) :=
        heis.irreducible inferInstance (monic_X_pow_sub_C ϖ hm_ne).isPrimitive
          (by rw [natDegree_X_pow_sub_C]; exact hm_pos)
      open Polynomial in
      have hirr_K : Irreducible (X ^ m - C (algebraMap A K ϖ) : Polynomial K) := by
        have := (monic_X_pow_sub_C ϖ hm_ne).irreducible_iff_irreducible_map_fraction_map
          (K := K) |>.mp hirr_A
        simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C] at this
        exact this
      open Polynomial in
      have hroot : aeval π (X ^ m - C (algebraMap A K ϖ) : Polynomial K) = 0 := by
        simp [map_sub, map_pow, aeval_X, aeval_C, hπ_pow]
      open Polynomial in
      have hminpoly : (X ^ m - C (algebraMap A K ϖ) : Polynomial K) = minpoly K π :=
        minpoly.eq_of_irreducible_of_monic hirr_K hroot
          (monic_X_pow_sub_C (algebraMap A K ϖ) hm_ne)
      open Polynomial in
      have hdeg : (minpoly K π).natDegree = m := by
        rw [← hminpoly, natDegree_X_pow_sub_C]
      rw [IntermediateField.adjoin.finrank (IsIntegral.of_finite K π), hdeg]
    exact ⟨algebraMap A K ϖ, π, hπ_pow, hπA_img_ne, hπ_ne, step_iii, ⟨ϖ, hϖ_irr, rfl⟩⟩
  obtain ⟨πA_img, π, hπm, hπA_ne, hπ_ne, hrank_Kπ, hπA_irr_info⟩ := core
  refine ⟨πA_img, π, hπm, hπA_ne, hπ_ne, hrank_Kπ, ?_, hπA_irr_info⟩
  set F := IntermediateField.adjoin K ({π} : Set L)
  have htower : Module.finrank K L = Module.finrank K F * Module.finrank F L := by
    rw [← Module.finrank_mul_finrank K (↥F) L]
  rw [hma, hrank_Kπ] at htower
  have hm_pos : 0 < m := by
    obtain rfl | h := Nat.eq_zero_or_pos m
    · simp only [zero_mul] at hma
      linarith [Module.finrank_pos (R := K) (M := L)]
    · exact h
  exact mul_left_cancel₀ (Nat.pos_iff_ne_zero.mp hm_pos) htower.symm

/--
[uniformizerPreimage](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RamificationTypes.lean)
-/
@[path]
lemma uniformizerPreimage
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A L]
  [IsScalarTower A B L]
  [IsScalarTower A K L]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
  {πA_img : K}
-- given
  (htotram : AKLB_ramIdx A B = Module.finrank K L)
  (hπA : algebraMap K L πA_img ≠ 0)
  (hπA_img : ∃ πA : A, Irreducible πA ∧ algebraMap A K πA = πA_img) :
-- imply
  ∃ πA : A, algebraMap A K πA = πA_img ∧ πA ∈ IsLocalRing.maximalIdeal A ∧ πA ∉ (IsLocalRing.maximalIdeal A) ^ 2 := by
-- proof
  obtain ⟨πA, hπA_irr, hπA_eq⟩ := hπA_img
  refine ⟨πA, hπA_eq, ?_, ?_⟩
  ·
    have h := hπA_irr.maximalIdeal_eq (R := A)
    rw [h]
    exact Ideal.subset_span (Set.mem_singleton πA)
  ·
    have h := hπA_irr.maximalIdeal_eq (R := A)
    rw [h, Ideal.span_singleton_pow]
    intro hmem
    rw [Ideal.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    have hne : πA ≠ 0 := hπA_irr.ne_zero
    have h1 : πA * (πA * c) = πA := by
      calc πA * (πA * c) = πA ^ 2 * c := by ring
      _ = πA := hc.symm
    have h2 : πA * c = 1 :=
      mul_left_cancel₀ hne (h1.trans (mul_one πA).symm)
    exact hπA_irr.not_isUnit ⟨⟨πA, c, h2, by rw [mul_comm]; exact h2⟩, rfl⟩

/--
[irreducible_xm_sub_uniformizer](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RamificationTypes.lean)
-/
@[path]
lemma irreducible_xm_sub_uniformizer
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A L]
  [IsScalarTower A B L]
  [IsScalarTower A K L]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
  {πA_img : K}
  {m : ℕ}
-- given
  (htotram : AKLB_ramIdx A B = Module.finrank K L)
  (hπA : algebraMap K L πA_img ≠ 0)
  (hπA_img : ∃ πA : A, Irreducible πA ∧ algebraMap A K πA = πA_img)
  (hm : ¬ (AKLB_residueChar A ∣ m))
  (hm_pos : 0 < m) :
-- imply
  Irreducible (Polynomial.X ^ m - Polynomial.C πA_img : Polynomial K) := by
-- proof
  obtain ⟨πA, hπA_eq, hπA_mem, hπA_sq⟩ :=
    uniformizerPreimage A K B L htotram πA_img hπA hπA_img
  set f : Polynomial A := Polynomial.X ^ m - Polynomial.C πA with hf_def
  have hf_monic : f.Monic := Polynomial.monic_X_pow_sub_C πA (by omega)
  have hf_deg : f.natDegree = m := Polynomial.natDegree_X_pow_sub_C
  have hf_eis : f.IsEisensteinAt (IsLocalRing.maximalIdeal A) := by
    constructor
    ·
      rw [Polynomial.Monic.leadingCoeff hf_monic]
      exact fun h => (IsLocalRing.maximalIdeal.isMaximal (R := A)).ne_top
        (Ideal.eq_top_of_isUnit_mem _ h isUnit_one)
    ·
      intro n hn
      rw [hf_deg] at hn
      simp only [f, Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
      have hne : n ≠ m := by omega
      simp only [if_neg hne]
      by_cases h0 : n = 0
      · simp [h0, hπA_mem]
      · simp [h0]
    ·
      simp only [f, Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
      have hne : (0 : ℕ) ≠ m := by omega
      simp only [if_neg hne, zero_sub]
      intro h
      exact hπA_sq (neg_mem_iff.mp h)
  have hirr_A : Irreducible f :=
    hf_eis.irreducible (IsLocalRing.maximalIdeal.isMaximal (R := A)).isPrime
      hf_monic.isPrimitive (by rw [hf_deg]; omega)
  have hirr_K : Irreducible (f.map (algebraMap A K)) :=
    hf_monic.irreducible_iff_irreducible_map_fraction_map.mp hirr_A
  have hmap : f.map (algebraMap A K) = Polynomial.X ^ m - Polynomial.C πA_img := by
    simp [f, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, hπA_eq]
  rwa [hmap] at hirr_K

/--
[tameWildDecomposition_existence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RamificationTypes.lean)
-/
@[path]
lemma tameWildDecomposition_existence
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A L]
  [IsScalarTower A B L]
  [IsScalarTower A K L]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
  {m a : ℕ}
-- given
  (htotram : AKLB_ramIdx A B = Module.finrank K L)
  (hma : Module.finrank K L = m * (AKLB_residueChar A) ^ a)
  (hm : ¬ (AKLB_residueChar A ∣ m)) :
-- imply
  ∃ (T : IntermediateField K L), Module.finrank K T = m ∧ Module.finrank T L = (AKLB_residueChar A) ^ a := by
-- proof
  obtain ⟨πA_img, π, _, _, _, hT_deg, hT_wild, _⟩ :=
    hensel_uniformizer_construction A K B L htotram m a hma hm
  exact ⟨IntermediateField.adjoin K ({π} : Set L), hT_deg, hT_wild⟩
end TameWildDecompositionTotallyRamified
section TameWildDecompositionGeneral

/--
[ramIdx_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RamificationTypes.lean)
-/
@[path]
lemma ramIdx_mul
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A L]
  [IsScalarTower A B L]
  [IsScalarTower A K L]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
  {E : IntermediateField K L} :
-- imply
  AKLB_ramIdx A B = ramIdx_over A B E * ramIdx_sub A B E := by
-- proof
  set C := integralClosure A ↥E
  haveI hDVR : IsDiscreteValuationRing ↥C := AKLB_intClE_isDVR A K L E
  letI : Algebra ↥C B := (intClE_to_B_algHom A B E).toAlgebra
  haveI : IsScalarTower A ↥C B := IsScalarTower.of_algHom (intClE_to_B_algHom A B E)
  set p := IsLocalRing.maximalIdeal A
  set P := IsLocalRing.maximalIdeal ↥C
  set Q := IsLocalRing.maximalIdeal B
  show p.ramificationIdx Q = P.ramificationIdx Q * p.ramificationIdx P
  have hinj_CB : Function.Injective (algebraMap ↥C B) := by
    change Function.Injective (intClE_to_B_algHom A B E)
    intro x y hxy
    have hinj_L : Function.Injective (intClE_to_L_algHom A E) := by
      intro a b hab
      unfold intClE_to_L_algHom at hab
      simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars'] at hab
      exact Subtype.val_injective (Subtype.val_injective hab)
    apply hinj_L
    have hBL : Function.Injective (algebraMap B L) := IsFractionRing.injective B L
    have key : ∀ z : ↥C, (intClE_to_L_algHom A E) z =
      algebraMap B L (intClE_to_B_algHom A B E z) := by
      intro z
      unfold intClE_to_B_algHom
      letI : Algebra ↥C L := (intClE_to_L_algHom A E).toAlgebra
      haveI : IsScalarTower A ↥C L := IsScalarTower.of_algHom (intClE_to_L_algHom A E)
      haveI : Algebra.IsIntegral A ↥C := integralClosure.AlgebraIsIntegral
      rw [IsIntegralClosure.algebraMap_lift A B L z]
      rfl
    rw [key x, key y, hxy]
  haveI : FaithfulSMul ↥C B :=
    (faithfulSMul_iff_algebraMap_injective ↥C B).mpr hinj_CB
  haveI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  haveI : Algebra.IsIntegral ↥C B := Algebra.IsIntegral.tower_top A
  haveI : IsLocalHom (algebraMap ↥C B) := Algebra.IsIntegral.isLocalHom ↥C B
  have hg : Ideal.map (algebraMap ↥C B) P ≤ Q :=
    IsLocalRing.map_maximalIdeal_le (algebraMap ↥C B)
  have hg0 : Ideal.map (algebraMap ↥C B) P ≠ ⊥ := by
    haveI : Module.IsTorsionFree ↥C B :=
      (Module.isTorsionFree_iff_faithfulSMul).mpr inferInstance
    exact Ideal.map_ne_bot_of_ne_bot (IsDiscreteValuationRing.not_a_field ↥C)
  have hfg : Ideal.map (algebraMap A B) p ≠ ⊥ := by
    intro h; apply IsDiscreteValuationRing.not_a_field A; rw [eq_bot_iff]
    intro x hx; rw [Submodule.mem_bot]; by_contra hx0
    have hmem := Ideal.mem_map_of_mem (algebraMap A B) hx; rw [h] at hmem
    exact hx0 (FaithfulSMul.algebraMap_injective A B
      (by rw [Ideal.mem_bot.mp hmem, map_zero]))
  rw [Ideal.ramificationIdx_algebra_tower hg0 hfg hg, mul_comm]
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 80000 in

/--
[ramIdx_over_eq_finrank_of_above_maxUnram](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RamificationTypes.lean)
-/
@[path]
lemma ramIdx_over_eq_finrank_of_above_maxUnram
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A L]
  [IsScalarTower A B L]
  [IsScalarTower A K L]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
  {E : IntermediateField K L}
-- given
  (hE : maximalUnramifiedSubextension A K L ≤ E) :
-- imply
  ramIdx_over A B E = Module.finrank E L := by
-- proof
  set F₀ := maximalUnramifiedSubextension A K L
  set C_E := integralClosure A ↥E
  haveI hDVR_CE : IsDiscreteValuationRing ↥C_E := AKLB_intClE_isDVR A K L E
  letI algCEB : Algebra ↥C_E B := (intClE_to_B_algHom A B E).toAlgebra
  haveI : IsScalarTower A ↥C_E B := IsScalarTower.of_algHom (intClE_to_B_algHom A B E)
  have hinj_CB : Function.Injective (algebraMap ↥C_E B) := by
    change Function.Injective (intClE_to_B_algHom A B E)
    intro x y hxy
    have hinj_L : Function.Injective (intClE_to_L_algHom A E) := by
      intro a b hab
      unfold intClE_to_L_algHom at hab
      simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars'] at hab
      exact Subtype.val_injective (Subtype.val_injective hab)
    apply hinj_L
    have key : ∀ z : ↥C_E, (intClE_to_L_algHom A E) z =
      algebraMap B L (intClE_to_B_algHom A B E z) := by
      intro z
      unfold intClE_to_B_algHom
      letI : Algebra ↥C_E L := (intClE_to_L_algHom A E).toAlgebra
      haveI : IsScalarTower A ↥C_E L := IsScalarTower.of_algHom (intClE_to_L_algHom A E)
      haveI : Algebra.IsIntegral A ↥C_E := integralClosure.AlgebraIsIntegral
      rw [IsIntegralClosure.algebraMap_lift A B L z]
      rfl
    rw [key x, key y, hxy]
  haveI : FaithfulSMul ↥C_E B :=
    (faithfulSMul_iff_algebraMap_injective ↥C_E B).mpr hinj_CB
  haveI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  haveI : Algebra.IsIntegral ↥C_E B := Algebra.IsIntegral.tower_top A
  haveI : IsLocalHom (algebraMap ↥C_E B) := Algebra.IsIntegral.isLocalHom ↥C_E B
  haveI : (IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal ↥C_E) :=
    IsLocalRing.ResidueField.instLiesOverMaximalIdeal
  haveI : FiniteDimensional K ↥E := IntermediateField.finiteDimensional_left E
  haveI : FiniteDimensional (↥E) L := IntermediateField.finiteDimensional_right E
  haveI : Algebra.IsSeparable K ↥E := IntermediateField.isSeparable_tower_bot K E
  haveI : IsFractionRing ↥C_E ↥E :=
    integralClosure.isFractionRing_of_finite_extension K ↥E
  haveI : IsNoetherian A ↥C_E :=
    IsIntegralClosure.isNoetherian A K ↥E (integralClosure A ↥E)
  haveI : Module.Finite A ↥C_E := inferInstance
  letI algCEL : Algebra ↥C_E L := (intClE_to_L_algHom A E).toAlgebra
  haveI : IsScalarTower A ↥C_E L := IsScalarTower.of_algHom (intClE_to_L_algHom A E)
  haveI : IsScalarTower ↥C_E ↥E L := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    show algebraMap ↥E L (algebraMap ↥C_E ↥E x) = (intClE_to_L_algHom A E) x
    unfold intClE_to_L_algHom
    simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars', Subalgebra.coe_val]
    rfl
  haveI : IsScalarTower ↥C_E B L := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change (intClE_to_L_algHom A E) x = algebraMap B L (intClE_to_B_algHom A B E x)
    unfold intClE_to_B_algHom
    letI : Algebra ↥C_E L := (intClE_to_L_algHom A E).toAlgebra
    haveI : IsScalarTower A ↥C_E L := IsScalarTower.of_algHom (intClE_to_L_algHom A E)
    haveI : Algebra.IsIntegral A ↥C_E := integralClosure.AlgebraIsIntegral
    rw [IsIntegralClosure.algebraMap_lift A B L x]; rfl
  haveI : IsDedekindDomain ↥C_E := by
    haveI : Ring.DimensionLEOne ↥C_E :=
      Ring.DimensionLEOne.isIntegralClosure A ↥E (integralClosure A ↥E)
    haveI : IsIntegrallyClosed ↥C_E :=
      integralClosure.isIntegrallyClosedOfFiniteExtension K
    exact {}
  haveI : Module.Finite ↥C_E B := Module.Finite.of_restrictScalars_finite A ↥C_E B
  have hCE_ne_bot : IsLocalRing.maximalIdeal ↥C_E ≠ ⊥ :=
    IsDiscreteValuationRing.not_a_field ↥C_E
  have hfund := @Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing
    (↥C_E) C_E.toCommRing B _ algCEB _ (↥E) L _ _ ‹IsDedekindDomain ↥C_E› _
    ‹IsFractionRing ↥C_E ↥E› _ _ _ algCEL ‹IsScalarTower ↥C_E B L›
    ‹IsScalarTower ↥C_E ↥E L› ‹Module.Finite ↥C_E B› _ _ _ hCE_ne_bot
  rw [Ideal.inertiaDeg_algebraMap] at hfund
  set C_F₀ := integralClosure A ↥F₀
  haveI hDVR_CF₀ : IsDiscreteValuationRing ↥C_F₀ := AKLB_intClE_isDVR A K L F₀
  obtain ⟨E₀, hE₀_unram, hE₀_deg, hE₀_max, _⟩ := thm_10_13_maxUnram_eq_resDeg A K B L
  have hF₀_eq_E₀ : F₀ = E₀ := by
    apply le_antisymm
    · exact iSup₂_le fun E hE => hE₀_max E hE
    · exact le_iSup₂ (f := fun E (_ : IsFiniteUnramifiedSubext A K L E) => E) E₀ hE₀_unram
  subst hF₀_eq_E₀
  letI algCF₀B : Algebra ↥C_F₀ B := (intClE_to_B_algHom A B F₀).toAlgebra
  haveI inst_st_A_CF₀_B : IsScalarTower A ↥C_F₀ B :=
    IsScalarTower.of_algHom (intClE_to_B_algHom A B F₀)
  have hinj_CF₀B : Function.Injective (algebraMap ↥C_F₀ B) := by
    change Function.Injective (intClE_to_B_algHom A B F₀)
    intro x y hxy
    have hinj_L : Function.Injective (intClE_to_L_algHom A F₀) := by
      intro a b hab
      unfold intClE_to_L_algHom at hab
      simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars'] at hab
      exact Subtype.val_injective (Subtype.val_injective hab)
    apply hinj_L
    have key : ∀ z : ↥C_F₀, (intClE_to_L_algHom A F₀) z =
      algebraMap B L (intClE_to_B_algHom A B F₀ z) := by
      intro z; unfold intClE_to_B_algHom
      letI : Algebra ↥C_F₀ L := (intClE_to_L_algHom A F₀).toAlgebra
      haveI : IsScalarTower A ↥C_F₀ L := IsScalarTower.of_algHom (intClE_to_L_algHom A F₀)
      haveI : Algebra.IsIntegral A ↥C_F₀ := integralClosure.AlgebraIsIntegral
      rw [IsIntegralClosure.algebraMap_lift A B L z]; rfl
    rw [key x, key y, hxy]
  haveI : FaithfulSMul ↥C_F₀ B :=
    (faithfulSMul_iff_algebraMap_injective ↥C_F₀ B).mpr hinj_CF₀B
  haveI : Algebra.IsIntegral ↥C_F₀ B := Algebra.IsIntegral.tower_top A
  haveI inst_lh_CF₀B : IsLocalHom (algebraMap ↥C_F₀ B) :=
    Algebra.IsIntegral.isLocalHom ↥C_F₀ B
  haveI : (IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal ↥C_F₀) :=
    IsLocalRing.ResidueField.instLiesOverMaximalIdeal
  have hf_CF₀B : Module.finrank
    (IsLocalRing.ResidueField ↥C_F₀) (IsLocalRing.ResidueField B) = 1 :=
    AKLB_resDeg_over_eq_one A K B L F₀ hE₀_unram hE₀_deg
  letI inclF₀E : ↥F₀ →ₐ[A] ↥E :=
    (IntermediateField.inclusion hE).restrictScalars A
  letI algCF₀E : Algebra ↥C_F₀ ↥E :=
    (inclF₀E.comp (integralClosure A ↥F₀).val).toAlgebra
  haveI : IsScalarTower A ↥C_F₀ ↥E :=
    IsScalarTower.of_algHom (inclF₀E.comp (integralClosure A ↥F₀).val)
  haveI : Algebra.IsIntegral A ↥C_F₀ := integralClosure.AlgebraIsIntegral
  let φ_CF₀_CE : ↥C_F₀ →ₐ[A] ↥C_E := IsIntegralClosure.lift A (↥C_E) (↥E)
  letI algCF₀CE : Algebra ↥C_F₀ ↥C_E := φ_CF₀_CE.toAlgebra
  haveI : IsScalarTower ↥C_F₀ ↥C_E B := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    apply IsFractionRing.injective B L
    conv_lhs => rw [show algebraMap ↥C_F₀ B x = intClE_to_B_algHom A B F₀ x from rfl]
    conv_rhs => rw [show algebraMap ↥C_F₀ ↥C_E x = φ_CF₀_CE x from rfl,
      show algebraMap ↥C_E B (φ_CF₀_CE x) =
        intClE_to_B_algHom A B E (φ_CF₀_CE x) from rfl]
    unfold intClE_to_B_algHom
    letI algCF₀L' : Algebra ↥C_F₀ L := (intClE_to_L_algHom A F₀).toAlgebra
    haveI : IsScalarTower A ↥C_F₀ L := IsScalarTower.of_algHom (intClE_to_L_algHom A F₀)
    rw [IsIntegralClosure.algebraMap_lift A B L x]
    haveI : Algebra.IsIntegral A ↥C_E := integralClosure.AlgebraIsIntegral
    rw [IsIntegralClosure.algebraMap_lift A B L (φ_CF₀_CE x)]
    show (intClE_to_L_algHom A F₀) x = (intClE_to_L_algHom A E) (φ_CF₀_CE x)
    unfold intClE_to_L_algHom
    simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars', Subalgebra.coe_val]
    have hlift := IsIntegralClosure.algebraMap_lift A (↥C_E) (↥E) x
    change (F₀.val : ↥F₀ → L) ↑x = (E.val : ↥E → L) ↑(φ_CF₀_CE x)
    rw [show (↑(φ_CF₀_CE x) : ↥E) = algebraMap ↥C_E ↥E (φ_CF₀_CE x) from rfl]
    rw [hlift]
    rfl
  haveI : IsLocalHom (algebraMap ↥C_F₀ ↥C_E) := by
    have hcomp : IsLocalHom ((algebraMap ↥C_E B).comp (algebraMap ↥C_F₀ ↥C_E)) := by
      rwa [← IsScalarTower.algebraMap_eq ↥C_F₀ ↥C_E B]
    exact isLocalHom_of_comp _ (algebraMap ↥C_E B)
  haveI : (IsLocalRing.maximalIdeal ↥C_E).LiesOver (IsLocalRing.maximalIdeal ↥C_F₀) :=
    IsLocalRing.ResidueField.instLiesOverMaximalIdeal
  have htower := Ideal.inertiaDeg_algebra_tower
    (IsLocalRing.maximalIdeal ↥C_F₀) (IsLocalRing.maximalIdeal ↥C_E)
    (IsLocalRing.maximalIdeal B)
  rw [Ideal.inertiaDeg_algebraMap, Ideal.inertiaDeg_algebraMap, Ideal.inertiaDeg_algebraMap] at htower
  letI : Algebra (↥C_F₀ ⧸ IsLocalRing.maximalIdeal ↥C_F₀) (B ⧸ IsLocalRing.maximalIdeal B) :=
    Ideal.Quotient.algebraQuotientOfLEComap (le_of_eq
      (IsLocalRing.maximalIdeal_comap (algebraMap ↥C_F₀ B)).symm)
  letI : Module (↥C_F₀ ⧸ IsLocalRing.maximalIdeal ↥C_F₀) (B ⧸ IsLocalRing.maximalIdeal B) :=
    Algebra.toModule
  have hf_CF₀B' : Module.finrank
    (↥C_F₀ ⧸ IsLocalRing.maximalIdeal ↥C_F₀) (B ⧸ IsLocalRing.maximalIdeal B) = 1 :=
    hf_CF₀B
  rw [hf_CF₀B'] at htower
  letI : Algebra (↥C_E ⧸ IsLocalRing.maximalIdeal ↥C_E) (B ⧸ IsLocalRing.maximalIdeal B) :=
    Ideal.Quotient.algebraQuotientOfLEComap (le_of_eq
      (IsLocalRing.maximalIdeal_comap (algebraMap ↥C_E B)).symm)
  letI : Module (↥C_E ⧸ IsLocalRing.maximalIdeal ↥C_E) (B ⧸ IsLocalRing.maximalIdeal B) :=
    Algebra.toModule
  have hf_CEB : Module.finrank
    (↥C_E ⧸ IsLocalRing.maximalIdeal ↥C_E) (B ⧸ IsLocalRing.maximalIdeal B) = 1 := by
    exact Nat.eq_one_of_mul_eq_one_right (Nat.mul_comm _ _ ▸ htower.symm)
  rwa [hf_CEB, mul_one] at hfund
set_option maxHeartbeats 999999 in
set_option synthInstance.maxHeartbeats 400000 in

/--
[tameWildDecomposition_inSubTower](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RamificationTypes.lean)
-/
@[path]
lemma tameWildDecomposition_inSubTower
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A L]
  [IsScalarTower A B L]
  [IsScalarTower A K L]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
  {m a : ℕ}
-- given
  (hma : AKLB_ramIdx A B = m * (AKLB_residueChar A) ^ a)
  (hm : ¬ (AKLB_residueChar A ∣ m)) :
-- imply
  ∃ (T : IntermediateField (↥(maximalUnramifiedSubextension A K L)) L), Module.finrank T L = (AKLB_residueChar A) ^ a := by
-- proof
  set F₀ := maximalUnramifiedSubextension A K L with hF₀_def
  set C := integralClosure A ↥F₀ with hC_def
  haveI hDVR_C : IsDiscreteValuationRing ↥C := AKLB_intClE_isDVR A K L F₀
  letI algCB : Algebra ↥C B := (intClE_to_B_algHom A B F₀).toAlgebra
  haveI : IsScalarTower A ↥C B := IsScalarTower.of_algHom (intClE_to_B_algHom A B F₀)
  have hinj_CB : Function.Injective (algebraMap ↥C B) := by
    change Function.Injective (intClE_to_B_algHom A B F₀)
    intro x y hxy
    have hinj_L : Function.Injective (intClE_to_L_algHom A F₀) := by
      intro a b hab
      unfold intClE_to_L_algHom at hab
      simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars'] at hab
      exact Subtype.val_injective (Subtype.val_injective hab)
    apply hinj_L
    have key : ∀ z : ↥C, (intClE_to_L_algHom A F₀) z =
      algebraMap B L (intClE_to_B_algHom A B F₀ z) := by
      intro z
      unfold intClE_to_B_algHom
      letI : Algebra ↥C L := (intClE_to_L_algHom A F₀).toAlgebra
      haveI : IsScalarTower A ↥C L := IsScalarTower.of_algHom (intClE_to_L_algHom A F₀)
      haveI : Algebra.IsIntegral A ↥C := integralClosure.AlgebraIsIntegral
      rw [IsIntegralClosure.algebraMap_lift A B L z]
      rfl
    rw [key x, key y, hxy]
  haveI : FaithfulSMul ↥C B :=
    (faithfulSMul_iff_algebraMap_injective ↥C B).mpr hinj_CB
  haveI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  haveI : Algebra.IsIntegral ↥C B := Algebra.IsIntegral.tower_top A
  haveI : IsLocalHom (algebraMap ↥C B) := Algebra.IsIntegral.isLocalHom ↥C B
  haveI : (IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal ↥C) :=
    IsLocalRing.ResidueField.instLiesOverMaximalIdeal
  haveI : FiniteDimensional K ↥F₀ := IntermediateField.finiteDimensional_left F₀
  haveI : FiniteDimensional (↥F₀) L := IntermediateField.finiteDimensional_right F₀
  haveI : Algebra.IsSeparable K ↥F₀ := IntermediateField.isSeparable_tower_bot K F₀
  haveI : IsFractionRing ↥C ↥F₀ :=
    integralClosure.isFractionRing_of_finite_extension K ↥F₀
  haveI : IsNoetherian A ↥C :=
    IsIntegralClosure.isNoetherian A K ↥F₀ (integralClosure A ↥F₀)
  haveI : Module.Finite A ↥C := inferInstance
  letI algCL : Algebra ↥C L := (intClE_to_L_algHom A F₀).toAlgebra
  haveI : IsScalarTower A ↥C L := IsScalarTower.of_algHom (intClE_to_L_algHom A F₀)
  haveI : IsScalarTower ↥C ↥F₀ L := by
    apply IsScalarTower.of_algebraMap_eq; intro x
    show algebraMap ↥F₀ L (algebraMap ↥C ↥F₀ x) = (intClE_to_L_algHom A F₀) x
    unfold intClE_to_L_algHom
    simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars', Subalgebra.coe_val]; rfl
  haveI : IsScalarTower ↥C B L := by
    apply IsScalarTower.of_algebraMap_eq; intro x
    change (intClE_to_L_algHom A F₀) x = algebraMap B L (intClE_to_B_algHom A B F₀ x)
    unfold intClE_to_B_algHom
    letI : Algebra ↥C L := (intClE_to_L_algHom A F₀).toAlgebra
    haveI : IsScalarTower A ↥C L := IsScalarTower.of_algHom (intClE_to_L_algHom A F₀)
    haveI : Algebra.IsIntegral A ↥C := integralClosure.AlgebraIsIntegral
    rw [IsIntegralClosure.algebraMap_lift A B L x]; rfl
  haveI : IsDedekindDomain ↥C := by
    haveI : Ring.DimensionLEOne ↥C :=
      Ring.DimensionLEOne.isIntegralClosure A ↥F₀ (integralClosure A ↥F₀)
    haveI : IsIntegrallyClosed ↥C :=
      integralClosure.isIntegrallyClosedOfFiniteExtension K
    exact {}
  haveI : Module.Finite ↥C B := Module.Finite.of_restrictScalars_finite A ↥C B
  haveI : NoZeroSMulDivisors ↥C B := by
    constructor; intro a b hab
    rw [Algebra.smul_def] at hab
    obtain h | h := mul_eq_zero.mp hab
    · left; exact hinj_CB (by rwa [map_zero])
    · right; exact h
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal ↥C) ↥C :=
    integral_closure_isAdicComplete A K ↥F₀
  obtain ⟨E₀, hE₀_unram, hE₀_deg, hE₀_max, _⟩ :=
    thm_10_13_maxUnram_eq_resDeg A K B L
  have hF₀_eq_E₀ : F₀ = E₀ := by
    apply le_antisymm
    · exact iSup₂_le fun E hE => hE₀_max E hE
    · exact le_iSup₂ (f := fun E (_ : IsFiniteUnramifiedSubext A K L E) => E) E₀ hE₀_unram
  subst hF₀_eq_E₀
  have hf_one : Module.finrank
    (IsLocalRing.ResidueField ↥C) (IsLocalRing.ResidueField B) = 1 :=
    AKLB_resDeg_over_eq_one A K B L F₀ hE₀_unram hE₀_deg
  haveI : Algebra.IsSeparable (IsLocalRing.ResidueField ↥C) (IsLocalRing.ResidueField B) := by
    haveI : FiniteDimensional (IsLocalRing.ResidueField ↥C) (IsLocalRing.ResidueField B) :=
      FiniteDimensional.of_finrank_eq_succ (by omega : Module.finrank (IsLocalRing.ResidueField ↥C) (IsLocalRing.ResidueField B) = Nat.succ 0)
    rw [← Field.finSepDegree_eq_finrank_iff]
    have h1 := Field.finSepDegree_le_finrank (IsLocalRing.ResidueField ↥C) (IsLocalRing.ResidueField B)
    have h2 : 0 < Field.finSepDegree (IsLocalRing.ResidueField ↥C) (IsLocalRing.ResidueField B) :=
      Nat.pos_of_neZero _
    omega
  have hramIdx_eq : AKLB_ramIdx A B = Module.finrank (↥F₀) L :=
    (thm_10_23_part_ii_degree A K B L).symm
  have htotram : AKLB_ramIdx (↥C) B = Module.finrank (↥F₀) L := by
    have hro := ramIdx_over_eq_finrank_of_above_maxUnram A K B L F₀ (le_refl _)
    show ramIdx_over A B F₀ = Module.finrank (↥F₀) L
    exact hro
  have hma_sub : Module.finrank (↥F₀) L = m * (AKLB_residueChar A) ^ a := by
    linarith [hramIdx_eq, hma]
  have hchar : AKLB_residueChar (↥C) = AKLB_residueChar A := by
    unfold AKLB_residueChar
    haveI : IsLocalHom (algebraMap A ↥C) := by
      have : IsLocalHom ((algebraMap (↥C) B).comp (algebraMap A ↥C)) := by
        rw [← IsScalarTower.algebraMap_eq]; exact ‹IsLocalHom (algebraMap A B)›
      exact isLocalHom_of_comp _ (algebraMap ↥C B)
    haveI : CharP (IsLocalRing.ResidueField ↥C) (ringChar (IsLocalRing.ResidueField A)) :=
      charP_of_injective_algebraMap
        (algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField ↥C)).injective _
    exact ringChar.eq (IsLocalRing.ResidueField ↥C) (ringChar (IsLocalRing.ResidueField A))
  have hma_sub' : Module.finrank (↥F₀) L = m * (AKLB_residueChar (↥C)) ^ a := by
    rw [hchar]; exact hma_sub
  have hm' : ¬ (AKLB_residueChar (↥C) ∣ m) := by rw [hchar]; exact hm
  haveI : Algebra.IsSeparable (↥F₀) L :=
    Algebra.isSeparable_tower_top_of_isSeparable K (↥F₀) L
  have result := @tameWildDecomposition_existence (↥C) _ _ hDVR_C (↥F₀) _ _ ‹IsFractionRing ↥C ↥F₀› ‹IsAdicComplete (IsLocalRing.maximalIdeal ↥C) ↥C› B _ _ _ algCB ‹IsLocalHom (algebraMap (↥C) B)› ‹Module.Finite (↥C) B› ‹NoZeroSMulDivisors (↥C) B› L _ _ ‹FiniteDimensional (↥F₀) L› ‹Algebra.IsSeparable (↥F₀) L› _ ‹IsFractionRing B L› algCL ‹IsScalarTower (↥C) B L› ‹IsScalarTower (↥C) (↥F₀) L› ‹Algebra.IsSeparable (IsLocalRing.ResidueField (↥C)) (IsLocalRing.ResidueField B)› htotram m a hma_sub' hm'
  obtain ⟨T, _, hT_wild⟩ := result
  rw [hchar] at hT_wild
  exact ⟨T, hT_wild⟩

/--
[tameWildDecomposition_subTowerExistence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RamificationTypes.lean)
-/
@[path]
lemma tameWildDecomposition_subTowerExistence
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A L]
  [IsScalarTower A B L]
  [IsScalarTower A K L]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
  {m a : ℕ}
-- given
  (hma : AKLB_ramIdx A B = m * (AKLB_residueChar A) ^ a)
  (hm : ¬ (AKLB_residueChar A ∣ m)) :
-- imply
  ∃ (E : IntermediateField K L), maximalUnramifiedSubextension A K L ≤ E ∧ Module.finrank E L = (AKLB_residueChar A) ^ a := by
-- proof
  obtain ⟨T, hT_deg⟩ := tameWildDecomposition_inSubTower A K B L m a hma hm
  let F₀ := maximalUnramifiedSubextension A K L
  let E := T.restrictScalars K
  use E
  constructor
  · intro x hx
    rw [IntermediateField.mem_restrictScalars]
    exact T.algebraMap_mem ⟨x, hx⟩
  · show Module.finrank (↥(T.restrictScalars K)) L = _
    rwa [show Module.finrank (↥(T.restrictScalars K)) L = Module.finrank (↥T) L from by congr 1]

/--
[exists_intermediate_with_ramIdx_over_eq_pa](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RamificationTypes.lean)
-/
@[path]
lemma exists_intermediate_with_ramIdx_over_eq_pa
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A L]
  [IsScalarTower A B L]
  [IsScalarTower A K L]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
  {m a : ℕ}
-- given
  (hma : AKLB_ramIdx A B = m * (AKLB_residueChar A) ^ a)
  (hm : ¬ (AKLB_residueChar A ∣ m)) :
-- imply
  ∃ (E : IntermediateField K L), maximalUnramifiedSubextension A K L ≤ E ∧ ramIdx_over A B E = (AKLB_residueChar A) ^ a ∧ Module.finrank E L = (AKLB_residueChar A) ^ a := by
-- proof
  obtain ⟨E, hE_le, hE_deg⟩ := tameWildDecomposition_subTowerExistence A K B L m a hma hm
  have hE_ram : ramIdx_over A B E = Module.finrank E L :=
    ramIdx_over_eq_finrank_of_above_maxUnram A K B L E hE_le
  exact ⟨E, hE_le, by rw [hE_ram, hE_deg], hE_deg⟩

/--
[tameWildDecomposition_towerTranslation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RamificationTypes.lean)
-/
@[path]
lemma tameWildDecomposition_towerTranslation
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A L]
  [IsScalarTower A B L]
  [IsScalarTower A K L]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
  {m a : ℕ}
-- given
  (hma : AKLB_ramIdx A B = m * (AKLB_residueChar A) ^ a)
  (hm : ¬ (AKLB_residueChar A ∣ m)) :
-- imply
  ∃ (E : IntermediateField K L), maximalUnramifiedSubextension A K L ≤ E ∧ ramIdx_sub A B E = m ∧ ramIdx_over A B E = Module.finrank E L ∧ Module.finrank E L = (AKLB_residueChar A) ^ a := by
-- proof
  obtain ⟨E, hE_F, hE_ramover, hE_deg⟩ :=
    exists_intermediate_with_ramIdx_over_eq_pa A K B L m a hma hm
  have hE_totram : ramIdx_over A B E = Module.finrank E L := by
    rw [hE_ramover, hE_deg]
  have hmul := ramIdx_mul A K B L E
  have hE_sub : ramIdx_sub A B E = m := by
    rw [hma, hE_ramover] at hmul
    have hpa_pos : 0 < (AKLB_residueChar A) ^ a := by
      by_contra h
      push_neg at h
      interval_cases (AKLB_residueChar A) ^ a
      simp at hma
      have hef := AKLB_degree_eq_ramIdx_mul_resDeg A K B L
      rw [hma, zero_mul] at hef
      have := Module.finrank_pos (R := K) (M := L)
      omega
    have h : m * (AKLB_residueChar A) ^ a = ramIdx_sub A B E * (AKLB_residueChar A) ^ a := by
      rw [hmul, mul_comm]
    exact (Nat.eq_of_mul_eq_mul_right hpa_pos h).symm
  exact ⟨E, hE_F, hE_sub, hE_totram, hE_deg⟩

/--
[tameWildDecompositionGeneral_existence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RamificationTypes.lean)
-/
@[path]
lemma tameWildDecompositionGeneral_existence
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A L]
  [IsScalarTower A B L]
  [IsScalarTower A K L]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)] :
-- imply
  ∃ (E : IntermediateField K L), ¬ (AKLB_residueChar A ∣ ramIdx_sub A B E) ∧ ramIdx_over A B E = Module.finrank E L ∧ (∃ k : ℕ, ramIdx_over A B E = (AKLB_residueChar A) ^ k) ∧ maximalUnramifiedSubextension A K L ≤ E := by
-- proof
  have hef := AKLB_degree_eq_ramIdx_mul_resDeg A K B L
  have he_ne : AKLB_ramIdx A B ≠ 0 := by
    intro h; simp only [h, zero_mul] at hef
    exact absurd hef (by have := Module.finrank_pos (R := K) (M := L); omega)
  have hp_or := residueChar_prime_or_zero (IsLocalRing.ResidueField A)
  obtain ⟨m, a, hdecomp, hm⟩ := padic_decomp_exists (AKLB_ramIdx A B) he_ne
    (AKLB_residueChar A) hp_or
  obtain ⟨E, hE_F, hE_sub, hE_totram, hE_deg⟩ :=
    tameWildDecomposition_towerTranslation A K B L m a hdecomp hm
  exact ⟨E, hE_sub ▸ hm, hE_totram, ⟨a, hE_totram.trans hE_deg⟩, hE_F⟩
end TameWildDecompositionGeneral


-- created on 2026-10-23

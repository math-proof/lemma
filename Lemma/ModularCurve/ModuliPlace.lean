import Mathlib
import Lemma.ModularCurve.X0ModL
import Lemma.ModularCurve.QAdicPlaceMod
import Lemma.ModularCurve.ModuliPointMap
import Lemma.WeierstrassCurve.ReduceHom
import Lemma.WeierstrassCurve.CyclicQuotientJ
import Lemma.AlgebraicCurve.Correspondence
import Instance.ModularCurve_ModuliPlace
import Structure.ModularCurve_ModuliPlace

set_option autoImplicit false

noncomputable section

open IsLocalRing AlgebraicCurve WeierstrassCurve WeierstrassCurve.Affine

namespace ModularCurve

universe u

section Generators

variable (K : Type*) [Field K] (N : ℕ)


@[simp] theorem coe_jqNFull (d : ℕ) [NeZero d] (hd : d ∣ N) :
    (jqNFull K N d hd : LaurentSeries K) = jqNModC K d := rfl

theorem jqNFull_one : jqNFull K N 1 (one_dvd N) = jModElt K (jqModC_mem_full K N) :=
  Subtype.ext (jqNModC_one K)

theorem inclusion_jqNFull [NeZero N] {M : ℕ} [NeZero M] (hMN : M ∣ N) (d : ℕ) [NeZero d]
    (hd : d ∣ M) :
    IntermediateField.inclusion (full_degeneracyC_le K hMN) (jqNFull K M d hd) =
      jqNFull K N d (hd.trans hMN) := rfl

theorem jModElt_sub_algebraMap_ne_zero (c : K) :
    jModElt K (jqModC_mem_full K N) - algebraMap K (modularFunctionFieldFullC K N) c ≠ 0 := by
  intro h
  have h1 : (jqModC K : LaurentSeries K) - algebraMap K (LaurentSeries K) c = 0 := by
    have h2 := congrArg (fun f : modularFunctionFieldFullC K N => (f : LaurentSeries K)) h
    simpa [jModElt] using h2
  have h3 := congrArg (fun f : LaurentSeries K => f.coeff (-1)) h1
  simp only [HahnSeries.coeff_sub, coeff_jqModC_neg_one, algebraMap_laurentSeries_eq_single,
    HahnSeries.coeff_single_of_ne (show (-1 : ℤ) ≠ 0 by norm_num), sub_zero,
    HahnSeries.coeff_zero] at h3
  exact one_ne_zero h3

theorem ModuliPlaceAux.div_mul_div_cancel_of_dvd {d M N : ℕ} (hd : d ∣ M) (hMN : M ∣ N) (hM : M ≠ 0) :
    M / d * (N / M) = N / d := by
  rw [Nat.div_mul_div_comm hd hMN, mul_comm d M, Nat.mul_div_mul_left N d (Nat.pos_of_ne_zero hM)]

end Generators

namespace ComapPlace

variable {K F Ω : Type*} [Field K] [Field F] [Field Ω] [Algebra K Ω] (φ : F →+* Ω) (W : Place K Ω)

theorem mem_iff_ord_nonneg {a : Ω} (ha : a ≠ 0) : a ∈ W.toValuationSubring ↔ 0 ≤ W.ord a := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W.toValuationSubring
  constructor
  · intro hmem
    obtain ⟨n, u, hu⟩ :=
      IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
        (x := (⟨a, hmem⟩ : W.toValuationSubring)) (by simpa [Subtype.ext_iff] using ha) hπ
    have hcoe : a = ((u : W.toValuationSubring) : Ω) * ((π : Ω) ^ (n : ℤ)) := by
      have h := congrArg Subtype.val hu
      push_cast at h
      rw [zpow_natCast]
      exact h
    rw [hcoe, W.ord_unit_smul_zpow u hπ (n : ℤ)]
    exact Int.natCast_nonneg n
  · intro h
    obtain ⟨u, hu⟩ := W.exists_unit_mul_zpow ha hπ
    rw [hu, show W.ord a = (((W.ord a).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
      zpow_natCast]
    exact mul_mem (u : W.toValuationSubring).2 (pow_mem (π : W.toValuationSubring).2 _)

theorem ord_pos_of_mem_maximalIdeal {a : W.toValuationSubring}
    (ha : a ∈ maximalIdeal W.toValuationSubring) (ha0 : a ≠ 0) : 0 < W.ord (a : Ω) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W.toValuationSubring
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hπ
  have hn : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at hu
    exact (IsLocalRing.mem_maximalIdeal _).mp ha (hu ▸ u.isUnit)
  have hcoe : (a : Ω) = ((u : W.toValuationSubring) : Ω) * ((π : Ω) ^ (n : ℤ)) := by
    have h := congrArg Subtype.val hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, W.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact_mod_cast Nat.pos_of_ne_zero hn

def eIdx : ℕ := sInf {n : ℕ | 0 < n ∧ ∃ f : F, f ≠ 0 ∧ W.ord (φ f) = n}

variable {φ W}

theorem mem_comap_iff_ord_nonneg {f : F} (hf : f ≠ 0) :
    f ∈ W.toValuationSubring.comap φ ↔ 0 ≤ W.ord (φ f) := by
  rw [ValuationSubring.mem_comap]
  exact mem_iff_ord_nonneg W ((map_ne_zero φ).mpr hf)

theorem eIdx_le_ord {f : F} (hf : f ≠ 0) (hpos : 0 < W.ord (φ f)) :
    (eIdx φ W : ℤ) ≤ W.ord (φ f) := by
  have h := Nat.sInf_le
    (s := {n : ℕ | 0 < n ∧ ∃ f : F, f ≠ 0 ∧ W.ord (φ f) = n})
    (m := (W.ord (φ f)).toNat) ⟨by omega, f, hf, by omega⟩
  rw [eIdx]
  omega

theorem isUnit_mk_comap_iff {f : F} (hf : f ≠ 0) (hmem : f ∈ W.toValuationSubring.comap φ) :
    IsUnit (⟨f, hmem⟩ : W.toValuationSubring.comap φ) ↔ W.ord (φ f) = 0 := by
  constructor
  · rintro h
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp h
    have hb' : f * (b : F) = 1 := by
      simpa [Subtype.ext_iff] using hb
    have hbne : (b : F) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hb'
      exact zero_ne_one hb'
    have hsum : W.ord (φ f) + W.ord (φ (b : F)) = 0 := by
      rw [← W.ord_mul ((map_ne_zero φ).mpr hf) ((map_ne_zero φ).mpr hbne), ← map_mul, hb',
        map_one, W.ord_one]
    have h1 : 0 ≤ W.ord (φ f) := (mem_comap_iff_ord_nonneg hf).mp hmem
    have h2 : 0 ≤ W.ord (φ (b : F)) := (mem_comap_iff_ord_nonneg hbne).mp b.2
    omega
  · intro h0
    have hinv : f⁻¹ ∈ W.toValuationSubring.comap φ :=
      (mem_comap_iff_ord_nonneg (inv_ne_zero hf)).mpr (by rw [map_inv₀, W.ord_inv]; omega)
    exact ⟨⟨⟨f, hmem⟩, ⟨f⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hf),
      Subtype.ext (inv_mul_cancel₀ hf)⟩, rfl⟩

variable (hex : ∃ f : F, f ≠ 0 ∧ 0 < W.ord (φ f))
include hex

theorem eIdx_set_nonempty :
    {n : ℕ | 0 < n ∧ ∃ f : F, f ≠ 0 ∧ W.ord (φ f) = n}.Nonempty := by
  obtain ⟨f, hf0, hf⟩ := hex
  exact ⟨(W.ord (φ f)).toNat, by omega, f, hf0, by omega⟩

theorem eIdx_pos : 0 < eIdx φ W :=
  (Nat.sInf_mem (eIdx_set_nonempty hex)).1

theorem exists_ord_eq_eIdx : ∃ f : F, f ≠ 0 ∧ W.ord (φ f) = eIdx φ W :=
  (Nat.sInf_mem (eIdx_set_nonempty hex)).2

theorem eIdx_dvd_ord {f : F} (hf : f ≠ 0) : (eIdx φ W : ℤ) ∣ W.ord (φ f) := by
  obtain ⟨g, hg0, hge⟩ := exists_ord_eq_eIdx hex
  set e : ℤ := (eIdx φ W : ℤ) with he
  have hepos : 0 < e := by
    have := eIdx_pos hex
    omega
  set m : ℤ := W.ord (φ f) with hm
  set q : ℤ := m / e with hq
  have hgq : φ (g ^ (-q)) = (φ g) ^ (-q) := map_zpow₀ _ _ _
  have hr : W.ord (φ (f * g ^ (-q))) = m - e * q := by
    rw [map_mul, W.ord_mul ((map_ne_zero φ).mpr hf)
      (by rw [hgq]; exact zpow_ne_zero _ ((map_ne_zero φ).mpr hg0)), hgq, W.ord_zpow, hge,
      ← hm]
    ring
  have hmod := Int.emod_nonneg m (by omega : e ≠ 0)
  have hmod' := Int.emod_lt_of_pos m hepos
  have hbridge : m % e = m - e * q := by
    rw [hq]
    exact Int.emod_def m e
  rcases eq_or_lt_of_le (show (0 : ℤ) ≤ m - e * q by omega) with heq | hlt
  · exact ⟨q, by omega⟩
  · exfalso
    have hfg : f * g ^ (-q) ≠ 0 := mul_ne_zero hf (zpow_ne_zero _ hg0)
    have hle := eIdx_le_ord (φ := φ) (W := W) hfg (by omega)
    rw [hr, ← he] at hle
    omega

theorem irreducible_mk_comap {g : F} (hg0 : g ≠ 0) (hmem : g ∈ W.toValuationSubring.comap φ)
    (hge : W.ord (φ g) = eIdx φ W) :
    Irreducible (⟨g, hmem⟩ : W.toValuationSubring.comap φ) := by
  have hepos : 0 < eIdx φ W := eIdx_pos hex
  constructor
  · rw [isUnit_mk_comap_iff hg0 hmem, hge]
    omega
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    have hab' : g = a * b := by simpa [Subtype.ext_iff] using hab
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hg0 (by simpa using hab')
    have hb0 : b ≠ 0 := by
      rintro rfl
      exact hg0 (by simpa using hab')
    have hsum : W.ord (φ a) + W.ord (φ b) = eIdx φ W := by
      rw [← W.ord_mul ((map_ne_zero φ).mpr ha0) ((map_ne_zero φ).mpr hb0), ← map_mul, ← hab',
        hge]
    have ha' : 0 ≤ W.ord (φ a) := (mem_comap_iff_ord_nonneg ha0).mp ha
    have hb' : 0 ≤ W.ord (φ b) := (mem_comap_iff_ord_nonneg hb0).mp hb
    rcases eq_or_lt_of_le ha' with ha0' | hapos
    · exact Or.inl ((isUnit_mk_comap_iff ha0 ha).mpr ha0'.symm)
    rcases eq_or_lt_of_le hb' with hb0' | hbpos
    · exact Or.inr ((isUnit_mk_comap_iff hb0 hb).mpr hb0'.symm)
    exfalso
    have h1 := eIdx_le_ord (φ := φ) (W := W) ha0 hapos
    have h2 := eIdx_le_ord (φ := φ) (W := W) hb0 hbpos
    omega

theorem isPrincipalIdealRing_comap : IsPrincipalIdealRing (W.toValuationSubring.comap φ) := by
  obtain ⟨g, hg0, hge⟩ := exists_ord_eq_eIdx hex
  have hepos : 0 < eIdx φ W := eIdx_pos hex
  have hgmem : g ∈ W.toValuationSubring.comap φ :=
    (mem_comap_iff_ord_nonneg hg0).mpr (by omega)
  refine (IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨⟨g, hgmem⟩, irreducible_mk_comap hex hg0 hgmem hge, ?_⟩).toIsPrincipalIdealRing
  rintro ⟨f, hmem⟩ hx
  have hf : f ≠ 0 := by simpa [Subtype.ext_iff] using hx
  obtain ⟨c, hc⟩ := eIdx_dvd_ord hex hf
  have hnonneg : 0 ≤ W.ord (φ f) := (mem_comap_iff_ord_nonneg hf).mp hmem
  have hcnonneg : 0 ≤ c := by
    by_contra hneg
    have hcle : c ≤ -1 := by omega
    have : (eIdx φ W : ℤ) * c ≤ (eIdx φ W : ℤ) * -1 :=
      mul_le_mul_of_nonneg_left hcle (by omega)
    omega
  set n : ℕ := c.toNat with hn
  have hcn : (n : ℤ) = c := Int.toNat_of_nonneg hcnonneg
  refine ⟨n, ?_⟩
  have hgn : g ^ n ≠ 0 := pow_ne_zero _ hg0
  have hdiv0 : f / g ^ n ≠ 0 := div_ne_zero hf hgn
  have hu0 : W.ord (φ (f / g ^ n)) = 0 := by
    have hkey : φ (f / g ^ n) = φ f * (φ g) ^ (-(n : ℤ)) := by
      rw [div_eq_mul_inv, map_mul, map_inv₀, map_pow, ← zpow_natCast (φ g) n, ← zpow_neg]
    rw [hkey, W.ord_mul ((map_ne_zero φ).mpr hf) (zpow_ne_zero _ ((map_ne_zero φ).mpr hg0)),
      W.ord_zpow, hge, hc, ← hcn]
    ring
  have humem : f / g ^ n ∈ W.toValuationSubring.comap φ :=
    (mem_comap_iff_ord_nonneg hdiv0).mpr (le_of_eq hu0.symm)
  have hu : IsUnit (⟨f / g ^ n, humem⟩ : W.toValuationSubring.comap φ) :=
    (isUnit_mk_comap_iff hdiv0 humem).mpr hu0
  refine ⟨hu.unit, ?_⟩
  refine Subtype.ext ?_
  have hcoe : ((hu.unit : W.toValuationSubring.comap φ) : F) = f / g ^ n := by
    rw [IsUnit.unit_spec]
  push_cast
  rw [hcoe, mul_comm, div_mul_cancel₀]
  exact hgn

theorem comap_ne_top : W.toValuationSubring.comap φ ≠ ⊤ := by
  obtain ⟨f, hf0, hf⟩ := hex
  intro htop
  have : f⁻¹ ∈ W.toValuationSubring.comap φ := htop ▸ trivial
  rw [mem_comap_iff_ord_nonneg (inv_ne_zero hf0), map_inv₀, W.ord_inv] at this
  omega

variable [Algebra K F]

omit hex in

def place (hφ : ∀ c : K, φ (algebraMap K F c) = algebraMap K Ω c)
    (hex : ∃ f : F, f ≠ 0 ∧ 0 < W.ord (φ f)) : Place K F where
  toValuationSubring := W.toValuationSubring.comap φ
  algebraMap_mem' a := by
    rw [ValuationSubring.mem_comap, hφ]
    exact W.algebraMap_mem' a
  ne_top' := comap_ne_top hex
  isPrincipalIdealRing' := isPrincipalIdealRing_comap hex

omit hex in
@[simp] theorem place_toValuationSubring (hφ : ∀ c : K, φ (algebraMap K F c) = algebraMap K Ω c)
    (hex : ∃ f : F, f ≠ 0 ∧ 0 < W.ord (φ f)) :
    (place hφ hex).toValuationSubring = W.toValuationSubring.comap φ := rfl

theorem ord_place_pos (hφ : ∀ c : K, φ (algebraMap K F c) = algebraMap K Ω c)
    {f : F} (hf : f ≠ 0) (hpos : 0 < W.ord (φ f)) : 0 < (place hφ hex).ord f := by
  have hmem : f ∈ W.toValuationSubring.comap φ := (mem_comap_iff_ord_nonneg hf).mpr hpos.le
  have hnot : ¬IsUnit (⟨f, hmem⟩ : W.toValuationSubring.comap φ) := by
    rw [isUnit_mk_comap_iff hf hmem]
    omega
  have hne : (⟨f, hmem⟩ : W.toValuationSubring.comap φ) ≠ 0 := fun h0 =>
    hf (congrArg Subtype.val h0)
  have hmax : (⟨f, hmem⟩ : W.toValuationSubring.comap φ) ∈
      maximalIdeal (W.toValuationSubring.comap φ) := (IsLocalRing.mem_maximalIdeal _).mpr hnot
  exact ord_pos_of_mem_maximalIdeal (place hφ hex) (a := ⟨f, hmem⟩) hmax hne

end ComapPlace

section TestDatum

variable (K : Type u) [Field K] [DecidableEq K] (N : ℕ)


def IsModuliPlaceOf (x : ModuliPoint N K) (v : Place K (modularFunctionFieldFullC K N)) : Prop :=
  ∃ (Ω : Type u) (_ : Field Ω) (_ : DecidableEq Ω) (_ : Algebra K Ω) (D : ModuliTestDatum K N x Ω),
    v.toValuationSubring = D.W.toValuationSubring.comap D.emb.toRingHom

def moduliPlaceOfPoint (x : ModuliPoint N K) : Place K (modularFunctionFieldFullC K N) :=
  haveI := Classical.dec (∃ v, IsModuliPlaceOf K N x v)
  if h : ∃ v, IsModuliPlaceOf K N x v then h.choose else qInftyPlaceMod K (jqModC_mem_full K N)

def moduliPlace (E : WeierstrassCurve K) (C : AddSubgroup E.toAffine.Point) :
    Place K (modularFunctionFieldFullC K N) :=
  haveI := Classical.dec
    (E.IsElliptic ∧ ∃ g : E.toAffine.Point, addOrderOf g = N ∧ AddSubgroup.zmultiples g = C)
  if h : E.IsElliptic ∧ ∃ g : E.toAffine.Point, addOrderOf g = N ∧ AddSubgroup.zmultiples g = C then
    moduliPlaceOfPoint K N (Quot.mk _ (⟨E, h.1, h.2.choose, h.2.choose_spec.1⟩ : Gamma0Pair N K))
  else qInftyPlaceMod K (jqModC_mem_full K N)

end TestDatum

namespace ModuliTestDatum

variable {K : Type u} [Field K] [DecidableEq K] {N : ℕ} {x : ModuliPoint N K}
  {Ω : Type u} [Field Ω] [DecidableEq Ω] [Algebra K Ω] (D : ModuliTestDatum K N x Ω)

theorem isUnit_Δ : IsUnit D.curve.Δ := by
  have h := D.map_Δ_ne_zero
  rw [WeierstrassCurve.map_Δ] at h
  exact (residue_ne_zero_iff_isUnit _).mp h

theorem res_injective : Function.Injective D.res := D.res.injective

theorem res_surjective : Function.Surjective D.res := fun c => ⟨_, D.res_algebraMap c⟩

def resEquiv : ResidueField D.W.toValuationSubring ≃+* K :=
  RingEquiv.ofBijective D.res ⟨D.res_injective, D.res_surjective⟩

@[simp] theorem resEquiv_apply (a : ResidueField D.W.toValuationSubring) : D.resEquiv a = D.res a :=
  rfl

theorem algebraMap_res (a : ResidueField D.W.toValuationSubring) :
    algebraMap K (ResidueField D.W.toValuationSubring) (D.res a) = a :=
  D.res_injective (D.res_algebraMap _)

theorem res_residue_algebraMap (c : K) :
    D.res (residue D.W.toValuationSubring (algebraMap K D.W.toValuationSubring c)) = c :=
  D.res_algebraMap c

theorem res_residue_j : D.res (residue D.W.toValuationSubring D.curve.j) = x.j := by
  letI := Classical.decEq (ResidueField D.W.toValuationSubring)
  obtain ⟨hord, hx⟩ := D.reduction
  have h := congrArg ModuliPoint.j hx
  rw [ModuliPoint.j_map, ModuliPoint.j_mk, WeierstrassCurve.map_j] at h
  exact h

theorem emb_jqNFull_one :
    D.emb (jqNFull K N 1 (one_dvd N)) = (D.curve.map D.W.toValuationSubring.subtype).j := by
  letI := Classical.decEq (AlgebraicClosure Ω)
  have h := D.emb_jqNFull (AlgebraicClosure Ω) 1 (one_dvd N)
  rw [cyclicQuotientJ_one, WeierstrassCurve.map_c₄, WeierstrassCurve.map_Δ, ← map_pow,
    ← map_div₀] at h
  rw [(algebraMap Ω (AlgebraicClosure Ω)).injective h, WeierstrassCurve.j, div_eq_mul_inv, mul_comm,
    Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ']

theorem emb_jModElt :
    D.emb (jModElt K (jqModC_mem_full K N)) = ((D.curve.j : D.W.toValuationSubring) : Ω) := by
  rw [← jqNFull_one, emb_jqNFull_one, WeierstrassCurve.map_j]
  rfl

theorem emb_algebraMap (c : K) : D.emb (algebraMap K _ c) = algebraMap K Ω c := D.emb.commutes c

theorem emb_jModElt_sub :
    D.emb (jModElt K (jqModC_mem_full K N) - algebraMap K _ x.j) =
      ((D.curve.j - algebraMap K D.W.toValuationSubring x.j : D.W.toValuationSubring) : Ω) := by
  rw [map_sub, emb_jModElt, emb_algebraMap]
  rfl

theorem j_sub_mem_maximalIdeal :
    (D.curve.j - algebraMap K D.W.toValuationSubring x.j) ∈ maximalIdeal D.W.toValuationSubring := by
  rw [← residue_eq_zero_iff, ← map_eq_zero_iff _ D.res_injective, map_sub, map_sub, res_residue_j,
    res_residue_algebraMap, sub_self]

theorem ord_emb_jModElt_sub_pos :
    0 < D.W.ord (D.emb (jModElt K (jqModC_mem_full K N) - algebraMap K _ x.j)) := by
  rw [emb_jModElt_sub]
  refine ComapPlace.ord_pos_of_mem_maximalIdeal D.W D.j_sub_mem_maximalIdeal ?_
  intro h0
  have h1 : D.emb (jModElt K (jqModC_mem_full K N) - algebraMap K _ x.j) = 0 := by
    rw [emb_jModElt_sub, h0]; rfl
  exact jModElt_sub_algebraMap_ne_zero K N x.j ((map_eq_zero_iff _ D.emb.toRingHom.injective).mp h1)

theorem exists_ord_emb_pos :
    ∃ f : modularFunctionFieldFullC K N, f ≠ 0 ∧ 0 < D.W.ord (D.emb.toRingHom f) :=
  ⟨_, jModElt_sub_algebraMap_ne_zero K N x.j, D.ord_emb_jModElt_sub_pos⟩

def place : Place K (modularFunctionFieldFullC K N) :=
  ComapPlace.place (φ := D.emb.toRingHom) (W := D.W) (fun c => D.emb.commutes c) D.exists_ord_emb_pos

@[simp] theorem place_toValuationSubring :
    D.place.toValuationSubring = D.W.toValuationSubring.comap D.emb.toRingHom := rfl

theorem mem_place_iff (f : modularFunctionFieldFullC K N) :
    f ∈ D.place.toValuationSubring ↔ D.emb f ∈ D.W.toValuationSubring := Iff.rfl

theorem ord_place_jModElt_sub_pos :
    0 < D.place.ord (jModElt K (jqModC_mem_full K N) - algebraMap K _ x.j) :=
  ComapPlace.ord_place_pos D.exists_ord_emb_pos _ (jModElt_sub_algebraMap_ne_zero K N x.j)
    D.ord_emb_jModElt_sub_pos

theorem isModuliPlaceOf_place : IsModuliPlaceOf K N x D.place :=
  ⟨Ω, ‹_›, ‹_›, ‹_›, D, rfl⟩

variable {D} in
theorem isModuliPlaceOf_iff_eq_place {v : Place K (modularFunctionFieldFullC K N)} :
    v.toValuationSubring = D.W.toValuationSubring.comap D.emb.toRingHom ↔ v = D.place :=
  ⟨fun h => Place.ext h, fun h => h ▸ rfl⟩

theorem restrictAlong_place_toValuationSubring {F : Type*} [Field F] [Algebra K F]
    (φ : F →ₐ[K] modularFunctionFieldFullC K N) (hφ : φ.toRingHom.IsIntegral) :
    (D.place.restrictAlong φ hφ).toValuationSubring =
      D.W.toValuationSubring.comap (D.emb.toRingHom.comp φ.toRingHom) := rfl

theorem emb_jqNFull_self [NeZero N] (Ω' : Type u) [Field Ω'] [DecidableEq Ω'] [IsAlgClosed Ω']
    [Algebra Ω Ω'] :
    algebraMap Ω Ω' (D.emb (jqNFull K N N dvd_rfl)) =
      ((D.curve.map D.W.toValuationSubring.subtype).map (algebraMap Ω Ω')).cyclicQuotientJ
        (AddSubgroup.zmultiples (WeierstrassCurve.mapPoint (algebraMap Ω Ω') D.gen)) N := by
  rw [D.emb_jqNFull Ω' N dvd_rfl, Nat.div_self (Nat.pos_of_ne_zero (NeZero.ne N)), one_smul]

theorem addOrderOf_div_smul_gen [NeZero N] {d : ℕ} (hd : d ∣ N) :
    addOrderOf ((N / d) • D.gen) = d := by
  have hN : N ≠ 0 := NeZero.ne N
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hN)
  have hq : 0 < N / d := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hd) hd0
  rw [addOrderOf_nsmul' _ hq.ne', D.addOrderOf_gen, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hd),
    Nat.div_div_self hd hN]

section RestrictLevel

variable [NeZero N] {M : ℕ} [NeZero M]

omit [NeZero M] in

theorem addOrderOf_levelGen (hMN : M ∣ N) : addOrderOf ((N / M) • D.gen) = M :=
  D.addOrderOf_div_smul_gen hMN

theorem addOrderOf_reduceHom_levelGen (hMN : M ∣ N) :
    letI := Classical.decEq (ResidueField D.W.toValuationSubring)
    addOrderOf (reduceHom D.map_Δ_ne_zero ((N / M) • D.gen)) = M := by
  letI := Classical.decEq (ResidueField D.W.toValuationSubring)
  obtain ⟨hord, -⟩ := D.reduction
  have hN : N ≠ 0 := NeZero.ne N
  have hM0 : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hq : 0 < N / M := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hMN) hM0
  rw [map_nsmul, addOrderOf_nsmul' _ hq.ne', hord, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hMN),
    Nat.div_div_self hMN hN]

variable (hMN : M ∣ N) (x' : ModuliPoint M K)
  (hx' : letI := Classical.decEq (ResidueField D.W.toValuationSubring)
    ModuliPoint.map D.res
      (Quot.mk _ (⟨D.curve.map (residue D.W.toValuationSubring),
        ⟨isUnit_iff_ne_zero.mpr D.map_Δ_ne_zero⟩, reduceHom D.map_Δ_ne_zero ((N / M) • D.gen),
          D.addOrderOf_reduceHom_levelGen hMN⟩ :
            Gamma0Pair M (ResidueField D.W.toValuationSubring))) = x')

def restrictLevel : ModuliTestDatum K M x' Ω where
  W := D.W
  curve := D.curve
  map_Δ_ne_zero := D.map_Δ_ne_zero
  gen := (N / M) • D.gen
  addOrderOf_gen := D.addOrderOf_levelGen hMN
  res := D.res
  res_algebraMap := D.res_algebraMap
  reduction := ⟨D.addOrderOf_reduceHom_levelGen hMN, hx'⟩
  emb := D.emb.comp (IntermediateField.inclusion (full_degeneracyC_le K hMN))
  emb_jqNFull Ω' _ _ _ _ d _ hd := by
    have hsmul : (M / d) • ((N / M) • D.gen) = (N / d) • D.gen := by
      rw [smul_smul, ModuliPlaceAux.div_mul_div_cancel_of_dvd hd hMN (NeZero.ne M)]
    have h := D.emb_jqNFull Ω' d (hd.trans hMN)
    rw [← hsmul] at h
    exact h

@[simp] theorem restrictLevel_W : (D.restrictLevel hMN x' hx').W = D.W := rfl

@[simp] theorem restrictLevel_curve : (D.restrictLevel hMN x' hx').curve = D.curve := rfl

@[simp] theorem restrictLevel_gen : (D.restrictLevel hMN x' hx').gen = (N / M) • D.gen := rfl

@[simp] theorem restrictLevel_res : (D.restrictLevel hMN x' hx').res = D.res := rfl

@[simp] theorem restrictLevel_emb :
    (D.restrictLevel hMN x' hx').emb =
      D.emb.comp (IntermediateField.inclusion (full_degeneracyC_le K hMN)) :=
  rfl

theorem restrictLevel_emb_jqNFull (d : ℕ) [NeZero d] (hd : d ∣ M) :
    (D.restrictLevel hMN x' hx').emb (jqNFull K M d hd) = D.emb (jqNFull K N d (hd.trans hMN)) :=
  rfl

theorem restrictLevel_place_toValuationSubring :
    (D.restrictLevel hMN x' hx').place.toValuationSubring =
      D.place.toValuationSubring.comap
        (IntermediateField.inclusion (full_degeneracyC_le K hMN)).toRingHom := rfl

theorem restrictAlong_inclusion_place
    (hι : (IntermediateField.inclusion (full_degeneracyC_le K hMN)).toRingHom.IsIntegral) :
    D.place.restrictAlong (IntermediateField.inclusion (full_degeneracyC_le K hMN)) hι =
      (D.restrictLevel hMN x' hx').place :=
  Place.ext rfl

include hx' in

theorem isModuliPlaceOf_restrictAlong_inclusion
    (hι : (IntermediateField.inclusion (full_degeneracyC_le K hMN)).toRingHom.IsIntegral)
    {v : Place K (modularFunctionFieldFullC K N)}
    (hv : v.toValuationSubring = D.W.toValuationSubring.comap D.emb.toRingHom) :
    IsModuliPlaceOf K M x'
      (v.restrictAlong (IntermediateField.inclusion (full_degeneracyC_le K hMN)) hι) := by
  have hv' : v = D.place := Place.ext hv
  subst hv'
  refine ⟨Ω, ‹_›, ‹_›, ‹_›, D.restrictLevel hMN x' hx', ?_⟩
  exact congrArg Place.toValuationSubring (D.restrictAlong_inclusion_place hMN x' hx' hι)

end RestrictLevel

end ModuliTestDatum

section API

variable (K : Type u) [Field K] [DecidableEq K] (N : ℕ)

variable {K N} in

theorem IsModuliPlaceOf.ord_jModElt_sub_pos {x : ModuliPoint N K}
    {v : Place K (modularFunctionFieldFullC K N)} (hv : IsModuliPlaceOf K N x v) :
    0 < v.ord (jModElt K (jqModC_mem_full K N) - algebraMap K _ x.j) := by
  obtain ⟨Ω, _, _, _, D, hD⟩ := hv
  rw [ModuliTestDatum.isModuliPlaceOf_iff_eq_place.mp hD]
  exact D.ord_place_jModElt_sub_pos

theorem isModuliPlaceOf_moduliPlaceOfPoint {x : ModuliPoint N K}
    (h : ∃ v, IsModuliPlaceOf K N x v) : IsModuliPlaceOf K N x (moduliPlaceOfPoint K N x) := by
  rw [moduliPlaceOfPoint, dif_pos h]
  exact h.choose_spec

theorem moduliPlaceOfPoint_of_not_exists {x : ModuliPoint N K}
    (h : ¬∃ v, IsModuliPlaceOf K N x v) :
    moduliPlaceOfPoint K N x = qInftyPlaceMod K (jqModC_mem_full K N) := by
  rw [moduliPlaceOfPoint, dif_neg h]

theorem moduliPlaceOfPoint_eq_of_forall_eq {x : ModuliPoint N K}
    (huniq : ∀ v v', IsModuliPlaceOf K N x v → IsModuliPlaceOf K N x v' → v = v')
    {v : Place K (modularFunctionFieldFullC K N)} (hv : IsModuliPlaceOf K N x v) :
    moduliPlaceOfPoint K N x = v :=
  huniq _ _ (isModuliPlaceOf_moduliPlaceOfPoint K N ⟨v, hv⟩) hv

theorem ModuliTestDatum.moduliPlaceOfPoint_eq_place {x : ModuliPoint N K}
    (huniq : ∀ v v', IsModuliPlaceOf K N x v → IsModuliPlaceOf K N x v' → v = v')
    {Ω : Type u} [Field Ω] [DecidableEq Ω] [Algebra K Ω] (D : ModuliTestDatum K N x Ω) :
    moduliPlaceOfPoint K N x = D.place :=
  moduliPlaceOfPoint_eq_of_forall_eq K N huniq D.isModuliPlaceOf_place

theorem moduliPlace_of_not {E : WeierstrassCurve K} {C : AddSubgroup E.toAffine.Point}
    (h : ¬(E.IsElliptic ∧ ∃ g : E.toAffine.Point, addOrderOf g = N ∧ AddSubgroup.zmultiples g = C)) :
    moduliPlace K N E C = qInftyPlaceMod K (jqModC_mem_full K N) := by
  rw [moduliPlace, dif_neg h]

theorem moduliPlace_of_not_isElliptic {E : WeierstrassCurve K} (hE : ¬E.IsElliptic)
    (C : AddSubgroup E.toAffine.Point) :
    moduliPlace K N E C = qInftyPlaceMod K (jqModC_mem_full K N) :=
  moduliPlace_of_not K N fun h => hE h.1

variable {K N} in
omit [DecidableEq K] in

theorem ModuliPlaceAux.heq_vcInvFun_one (E : WeierstrassCurve K) (P : E.toAffine.Point) :
    HEq (Point.vcInvFun (1 : VariableChange K) E.toAffine P) P := by
  have hE : ((1 : VariableChange K) • E.toAffine).toAffine = E.toAffine := one_smul _ _
  cases P with
  | zero => exact Point.heq_zero hE
  | some x y h =>
    refine Point.heq_some hE ?_ ?_
    · simp [vcXInv, VariableChange.one_def]
    · simp [vcYInv, VariableChange.one_def]

variable {K N} in

theorem ModuliPoint.mk_eq_mk_of_zmultiples_eq [NeZero N] {E : WeierstrassCurve K} [hE : E.IsElliptic]
    {g g' : E.toAffine.Point} (hg : addOrderOf g = N) (hg' : addOrderOf g' = N)
    (h : AddSubgroup.zmultiples g = AddSubgroup.zmultiples g') :
    (Quot.mk _ (⟨E, hE, g, hg⟩ : Gamma0Pair N K) : ModuliPoint N K) =
      Quot.mk _ (⟨E, hE, g', hg'⟩ : Gamma0Pair N K) := by

  have hmem : g' ∈ AddSubgroup.zmultiples g := h ▸ AddSubgroup.mem_zmultiples g'
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
  have hN0 : N ≠ 0 := NeZero.ne N
  have hN : (N : ℤ) ≠ 0 := by exact_mod_cast hN0
  set a : ℕ := (m % (N : ℤ)).toNat with ha
  have ham : (a : ℤ) = m % (N : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg _ hN)
  set k : ℕ := a + N with hk
  have hag : a • g = g' := by
    rw [← hm, ← natCast_zsmul, ham, ← hg, mod_addOrderOf_zsmul]
  have hkg : k • g = g' := by
    rw [hk, add_nsmul, hag, ← hg, addOrderOf_nsmul_eq_zero, add_zero]
  have hk0 : k ≠ 0 := by
    rw [hk]; omega
  have hcop : k.Coprime N := by
    have h1 : addOrderOf (k • g) = N := by rw [hkg, hg']
    rw [addOrderOf_nsmul' g hk0, hg] at h1
    have h2 : N.gcd k = 1 := by
      have h3 := Nat.div_mul_cancel (Nat.gcd_dvd_left N k)
      rw [h1] at h3
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hN0) (h3.trans (mul_one N).symm)
    exact Nat.coprime_comm.mp h2
  refine Quot.sound ⟨1, one_smul _ _, k, hcop, ?_⟩

  show HEq g' (k • Point.vcInvFun (1 : VariableChange K) E.toAffine g)
  rw [← hkg]
  have hE1 : ((1 : VariableChange K) • E.toAffine).toAffine = E.toAffine := one_smul _ _
  exact (Point.heq_nsmul hE1 k (ModuliPlaceAux.heq_vcInvFun_one E g)).symm

theorem moduliPlace_zmultiples [NeZero N] (E : WeierstrassCurve K) [hE : E.IsElliptic]
    (g : E.toAffine.Point) (hg : addOrderOf g = N) :
    moduliPlace K N E (AddSubgroup.zmultiples g) =
      moduliPlaceOfPoint K N (Quot.mk _ (⟨E, hE, g, hg⟩ : Gamma0Pair N K)) := by
  have h : E.IsElliptic ∧ ∃ g' : E.toAffine.Point, addOrderOf g' = N ∧
      AddSubgroup.zmultiples g' = AddSubgroup.zmultiples g := ⟨hE, g, hg, rfl⟩
  rw [moduliPlace, dif_pos h]
  congr 1
  exact ModuliPoint.mk_eq_mk_of_zmultiples_eq h.2.choose_spec.1 hg h.2.choose_spec.2

theorem isModuliPlaceOf_moduliPlace [NeZero N] (E : WeierstrassCurve K) [hE : E.IsElliptic]
    (g : E.toAffine.Point) (hg : addOrderOf g = N)
    (h : ∃ v, IsModuliPlaceOf K N (Quot.mk _ (⟨E, hE, g, hg⟩ : Gamma0Pair N K)) v) :
    IsModuliPlaceOf K N (Quot.mk _ (⟨E, hE, g, hg⟩ : Gamma0Pair N K))
      (moduliPlace K N E (AddSubgroup.zmultiples g)) := by
  rw [moduliPlace_zmultiples K N E g hg]
  exact isModuliPlaceOf_moduliPlaceOfPoint K N h

theorem ord_moduliPlace_jModElt_sub_pos [NeZero N] (E : WeierstrassCurve K) [hE : E.IsElliptic]
    (g : E.toAffine.Point) (hg : addOrderOf g = N)
    (h : ∃ v, IsModuliPlaceOf K N (Quot.mk _ (⟨E, hE, g, hg⟩ : Gamma0Pair N K)) v) :
    0 < (moduliPlace K N E (AddSubgroup.zmultiples g)).ord
      (jModElt K (jqModC_mem_full K N) - algebraMap K _ E.j) :=
  (isModuliPlaceOf_moduliPlace K N E g hg h).ord_jModElt_sub_pos

end API

end ModularCurve

end

import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.ArithmeticGeometry.code.AdeleQuotientDim.Part2
open FunctionFieldAdeleRing DiscreteValuationFamily
open scoped RestrictedProduct


/--
[uniformizer_exists](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AdeleQuotientDim.lean)
-/
@[path]
lemma uniformizer_exists
  [DecidableEq P]
  [Field k]
  [Field F]
  [Algebra k F]
  {_O : P → ValuationSubring F}
  [DiscreteValuationFamily P F k]
  {p : P} :
-- imply
  ∃ t : F, DiscreteValuationFamily.ord (k := k) p t = (1 : ℤ) :=
-- proof
  DiscreteValuationFamily.uniformizer_exists (k := k) p

/--
[residueField_finiteDimensional](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AdeleQuotientDim.lean)
-/
@[path]
lemma residueField_finiteDimensional
  [DecidableEq P]
  [Field k]
  [Field F]
  [Algebra k F]
  {O : P → ValuationSubring F}
  [ConstantField k (F := F) (P := P) (O := O)]
  [FunctionFieldProperty F P O]
  [DiscreteValuationFamily P F k]
  {p : P} :
-- imply
  FiniteDimensional k (IsLocalRing.ResidueField ↥(O p)) :=
-- proof
  ConstantField.residueField_finiteDimensional p

/--
[placeDegree_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AdeleQuotientDim.lean)
-/
@[path]
lemma placeDegree_pos
  [DecidableEq P]
  [Field k]
  [Field F]
  [Algebra k F]
  {O : P → ValuationSubring F}
  [ConstantField k (F := F) (P := P) (O := O)]
  [FunctionFieldProperty F P O]
  [DiscreteValuationFamily P F k]
  {p : P} :
-- imply
  0 < placeDegree (F := F) (k := k) (O := O) p := by
-- proof
  unfold placeDegree
  haveI := residueField_finiteDimensional (F := F) (k := k) (O := O) p
  exact Module.finrank_pos

/--
[dvr_ord_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AdeleQuotientDim.lean)
-/
@[path]
lemma dvr_ord_one
  [Field k]
  [Field F]
  [Algebra k F]
  [DiscreteValuationFamily P F k]
  {p : P} :
-- imply
  DiscreteValuationFamily.ord (k := k) p (1 : F) = (0 : ℤ) := by
-- proof
  have := DiscreteValuationFamily.ord_algebraMap (k := k) (F := F) p (1 : k) one_ne_zero
  rwa [map_one] at this

/--
[dvr_ord_zpow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AdeleQuotientDim.lean)
-/
@[path]
lemma dvr_ord_zpow
  [Field k]
  [Field F]
  [Algebra k F]
  [DiscreteValuationFamily P F k]
  {p : P}
  {t : F}
  {m : ℤ}
-- given
  (ht : DiscreteValuationFamily.ord (k := k) p t = (1 : ℤ))
  (ht_ne : t ≠ 0) :
-- imply
  DiscreteValuationFamily.ord (k := k) p (t ^ m) = (m : ℤ) := by
-- proof
  have ht_inv : DiscreteValuationFamily.ord (k := k) p t⁻¹ = (-1 : ℤ) := by
    have hmul := DiscreteValuationFamily.ord_mul (k := k) p t t⁻¹
    rw [mul_inv_cancel₀ ht_ne, dvr_ord_one, ht] at hmul
    cases hv : DiscreteValuationFamily.ord (k := k) p t⁻¹ with
    | top => rw [hv] at hmul; simp at hmul
    | coe v =>
      rw [hv, ← WithTop.coe_add] at hmul
      have : (1 : ℤ) + v = 0 := by exact_mod_cast hmul.symm
      norm_cast; omega
  induction m using Int.induction_on with
  | zero => simp [zpow_zero, dvr_ord_one]
  | succ n ih =>
    rw [zpow_add_one₀ ht_ne, DiscreteValuationFamily.ord_mul, ih, ht,
      ← WithTop.coe_add]
  | pred n ih =>
    rw [zpow_sub_one₀ ht_ne, DiscreteValuationFamily.ord_mul, ih, ht_inv,
      ← WithTop.coe_add]; congr 1

/--
[adeleFromSingleComponent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AdeleQuotientDim.lean)
-/
@[path]
lemma adeleFromSingleComponent
  [DecidableEq P]
  [Field k]
  [Field F]
  [Algebra k F]
  {O : P → ValuationSubring F}
  [ConstantField k (F := F) (P := P) (O := O)]
  [FunctionFieldProperty F P O]
  [DiscreteValuationFamily P F k]
  {D : P → ℤ}
  {p₀ : P}
  {x : F}
-- given
  (hx : DiscreteValuationFamily.ord (k := k) p₀ x ≥ ↑(-(D p₀ + 1))) :
-- imply
  ∃ α : ↥(adeleSpace (F := F) (O := O) k (Function.update D p₀ (D p₀ + 1))), (α : FunctionFieldAdeleRing F P O) p₀ = x := by
-- proof
  set f : P → F := Function.update (fun _ => (0 : F)) p₀ x with hf_def
  have h_cofin : ∀ᶠ p in Filter.cofinite, f p ∈ O p := by
    rw [Filter.eventually_cofinite]
    apply Set.Finite.subset (Set.finite_singleton p₀)
    intro q hq
    simp only [Set.mem_setOf_eq] at hq
    simp only [Set.mem_singleton_iff]
    by_contra h
    exact hq (by rw [hf_def, Function.update_of_ne h]; exact (O q).toSubring.zero_mem)
  set α : FunctionFieldAdeleRing F P O := ⟨f, h_cofin⟩ with hα_def
  have h_mem : α ∈ adeleSpace (F := F) (O := O) k (Function.update D p₀ (D p₀ + 1)) := by
    intro q
    show DiscreteValuationFamily.ord (k := k) q (f q) ≥
      ↑(-(Function.update D p₀ (D p₀ + 1) q))
    by_cases hq : q = p₀
    · subst hq
      simp only [hf_def, Function.update_self, Function.update_self]
      exact hx
    · simp only [hf_def, Function.update_of_ne hq]
      simp only [DiscreteValuationFamily.ord_zero]
      exact le_top
  refine ⟨⟨α, h_mem⟩, ?_⟩
  show α p₀ = x
  simp only [hα_def, hf_def]
  change (Function.update (fun _ => (0 : F)) p₀ x) p₀ = x
  exact Function.update_self p₀ x (fun _ => (0 : F))

/--
[finrank_comap_chain](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AdeleQuotientDim.lean)
-/
@[path]
lemma finrank_comap_chain
  [DivisionRing R]
  [AddCommGroup M]
  [Module R M]
  {S T U : Submodule R M}
  [FiniteDimensional R (↥U ⧸ Submodule.comap U.subtype T)]
  [FiniteDimensional R (↥T ⧸ Submodule.comap T.subtype S)]
-- given
  (hST : S ≤ T)
  (hTU : T ≤ U) :
-- imply
  FiniteDimensional R (↥U ⧸ Submodule.comap U.subtype S) ∧ Module.finrank R (↥U ⧸ Submodule.comap U.subtype S) = Module.finrank R (↥T ⧸ Submodule.comap T.subtype S) + Module.finrank R (↥U ⧸ Submodule.comap U.subtype T) := by
-- proof
  set S' := Submodule.comap U.subtype S with hS'_def
  set T' := Submodule.comap U.subtype T with hT'_def
  have hS'T' : S' ≤ T' := Submodule.comap_mono hST
  let e := Submodule.comapSubtypeEquivOfLe hTU
  have hmap : Submodule.map e.toLinearMap (Submodule.comap T'.subtype S') =
    Submodule.comap T.subtype S := by
    ext ⟨x, hx⟩
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · rintro ⟨y, hy_mem, hy_eq⟩
      rw [← show (↑(e y) : M) = x from congr_arg Subtype.val hy_eq,
        Submodule.comapSubtypeEquivOfLe_apply_coe]
      exact hy_mem
    · intro hxS
      exact ⟨⟨⟨x, hTU hx⟩, hx⟩, hxS,
        Subtype.ext (Submodule.comapSubtypeEquivOfLe_apply_coe hTU _)⟩
  let qe := Submodule.Quotient.equiv _ _ e hmap
  haveI : FiniteDimensional R (↥T' ⧸ Submodule.comap T'.subtype S') :=
    Module.Finite.equiv qe.symm
  let f : ↥T' →ₗ[R] ↥U ⧸ S' := S'.mkQ.comp T'.subtype
  have hker_f : LinearMap.ker f = Submodule.comap T'.subtype S' := by
    ext ⟨x, hx⟩
    simp only [f, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]
  have hrange_f : LinearMap.range f = Submodule.map S'.mkQ T' := by
    ext y; simp only [f, LinearMap.mem_range, LinearMap.comp_apply, Submodule.subtype_apply]
    exact ⟨fun ⟨⟨x, hx⟩, h⟩ => ⟨x, hx, h⟩, fun ⟨x, hx, h⟩ => ⟨⟨x, hx⟩, h⟩⟩
  have h_re : (↥T' ⧸ Submodule.comap T'.subtype S') ≃ₗ[R] ↥(Submodule.map S'.mkQ T') := by
    rw [← hker_f, ← hrange_f]; exact f.quotKerEquivRange
  haveI : FiniteDimensional R ↥(Submodule.map S'.mkQ T') := Module.Finite.equiv h_re
  have h_iso := Submodule.quotientQuotientEquivQuotient S' T' hS'T'
  haveI : FiniteDimensional R ((↥U ⧸ S') ⧸ Submodule.map S'.mkQ T') :=
    Module.Finite.equiv h_iso.symm
  haveI : FiniteDimensional R (↥U ⧸ S') :=
    Module.Finite.of_submodule_quotient (Submodule.map S'.mkQ T')
  refine ⟨inferInstance, ?_⟩
  have h1 := Submodule.finrank_quotient_add_finrank (Submodule.map S'.mkQ T')
  rw [LinearEquiv.finrank_eq h_iso] at h1
  have h2 : Module.finrank R ↥(Submodule.map S'.mkQ T') =
    Module.finrank R (↥T' ⧸ Submodule.comap T'.subtype S') := (LinearEquiv.finrank_eq h_re).symm
  have h3 : Module.finrank R (↥T' ⧸ Submodule.comap T'.subtype S') =
    Module.finrank R (↥T ⧸ Submodule.comap T.subtype S) := LinearEquiv.finrank_eq qe
  omega
section Lemma22_8
variable {F : Type*} [Field F] {P : Type*} [DecidableEq P]
  {O : P → ValuationSubring F}
  (k : Type*) [Field k] [Algebra k F]
  [ConstantField k (F := F) (P := P) (O := O)]
  [FunctionFieldProperty F P O]
  [DiscreteValuationFamily P F k]

/--
[adeleSpace_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AdeleQuotientDim.lean)
-/
@[path]
lemma adeleSpace_mono
  [Field F]
  [DecidableEq P]
  {A B : P → ℤ}
-- given
  (hAB : ∀ p, A p ≤ B p) :
-- imply
  adeleSpace (F := F) (O := O) k A ≤ adeleSpace (F := F) (O := O) k B := by
-- proof
  intro α hα
  simp only [adeleSpace, Submodule.mem_mk] at *
  intro p
  exact le_trans (by exact_mod_cast neg_le_neg_iff.mpr (hAB p)) (hα p)
variable [HasResidueFieldSurjection P F k O]

/--
[adeleSpace_singleStep_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AdeleQuotientDim.lean)
-/
@[path]
lemma adeleSpace_singleStep_finrank
  [Field F]
  [DecidableEq P]
  [HasResidueFieldSurjection P F k O]
  {D : P → ℤ}
  {p₀ : P} :
-- imply
  let D' := Function.update D p₀ (D p₀ + 1) FiniteDimensional k (adeleSpace (F := F) (O := O) k D' ⧸ Submodule.comap (adeleSpace (F := F) (O := O) k D').subtype (adeleSpace (F := F) (O := O) k D)) ∧ Module.finrank k (adeleSpace (F := F) (O := O) k D' ⧸ Submodule.comap (adeleSpace (F := F) (O := O) k D').subtype (adeleSpace (F := F) (O := O) k D)) = HasResidueFieldSurjection.degPlace (F := F) (k := k) (O := O) p₀ := by
-- proof
  intro D'
  set φ := HasResidueFieldSurjection.φ (F := F) (O := O) (k := k) D p₀
  have hφ_surj := HasResidueFieldSurjection.φ_surj (F := F) (O := O) (k := k) D p₀
  have hφ_ker := HasResidueFieldSurjection.φ_ker (F := F) (O := O) (k := k) D p₀
  have h_equiv : (adeleSpace (F := F) (O := O) k D' ⧸ LinearMap.ker φ) ≃ₗ[k]
    LinearMap.range φ := φ.quotKerEquivRange
  have h_range_top : LinearMap.range φ = ⊤ := LinearMap.range_eq_top.mpr hφ_surj
  have h_equiv' : (adeleSpace (F := F) (O := O) k D' ⧸ LinearMap.ker φ) ≃ₗ[k]
    (Fin (HasResidueFieldSurjection.degPlace (F := F) (k := k) (O := O) p₀) → k) := by
    exact h_equiv.trans (LinearEquiv.ofTop _ h_range_top)
  rw [hφ_ker] at h_equiv'
  constructor
  ·
    exact Module.Finite.equiv h_equiv'.symm
  ·
    rw [LinearEquiv.finrank_eq h_equiv']
    simp

/--
[divisorDistance_sub_single_lt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AdeleQuotientDim.lean)
-/
@[path]
lemma divisorDistance_sub_single_lt
  [Field F]
  [DecidableEq P]
  [HasResidueFieldSurjection P F k O]
  {A B : P →₀ ℤ}
  {p : P}
-- given
  (hAB : ∀ p, A p ≤ B p)
  (_h_ne : B - A ≠ 0)
  (hp : p ∈ (B - A).support) :
-- imply
  divisorDistance A (B - Finsupp.single p 1) < divisorDistance A B := by
-- proof
  simp only [divisorDistance]
  have hBA_nonneg : ∀ q, 0 ≤ (B - A) q := fun q => by
    simp only [Finsupp.coe_sub, Pi.sub_apply]; linarith [hAB q]
  have hBAp_pos : (B - A) p ≥ 1 := by
    rw [Finsupp.mem_support_iff] at hp; have := hBA_nonneg p; omega
  have h_diff : (B - Finsupp.single p 1) - A = (B - A) - Finsupp.single p 1 := by
    ext q; simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_apply]; ring
  rw [h_diff]
  have h_sub : ((B - A) - Finsupp.single p 1).sum (fun _ n => n) =
    (B - A).sum (fun _ n => n) - 1 := by
    rw [Finsupp.sum_sub_index (fun _ b₁ b₂ => by ring)]
    rw [Finsupp.sum_single_index rfl]
  rw [h_sub]
  have h_sum_nonneg : (B - A).sum (fun _ n => n) ≥ 0 :=
    Finsupp.sum_nonneg (fun q _ => hBA_nonneg q)
  have h_sum_pos : (B - A).sum (fun _ n => n) ≥ 1 := by
    unfold Finsupp.sum
    calc ∑ x ∈ (B - A).support, (B - A) x ≥ (B - A) p :=
      Finset.single_le_sum (fun q _ => hBA_nonneg q) hp
      _ ≥ 1 := hBAp_pos
  omega

/--
[adeleComap_top_of_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AdeleQuotientDim.lean)
-/
@[path]
lemma adeleComap_top_of_eq
  [Field F]
  [DecidableEq P]
  [HasResidueFieldSurjection P F k O]
  {D : P → ℤ} :
-- imply
  adeleComap (F := F) (O := O) k D D = ⊤ := by
-- proof
  ext ⟨x, hx⟩
  simp only [adeleComap, Submodule.mem_comap, Submodule.subtype_apply,
    Submodule.mem_top, iff_true]
  exact hx

/--
[finrank_quotient_top_eq_zero'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AdeleQuotientDim.lean)
-/
@[path]
lemma finrank_quotient_top_eq_zero'
  [Field F]
  [DecidableEq P]
  [HasResidueFieldSurjection P F k O]
  [DivisionRing R]
  [AddCommGroup M]
  [Module R M] :
-- imply
  Module.finrank R (M ⧸ (⊤ : Submodule R M)) = 0 := by
-- proof
  haveI : Subsingleton (M ⧸ (⊤ : Submodule R M)) :=
    Submodule.Quotient.subsingleton_iff.mpr rfl
  exact Module.finrank_zero_of_subsingleton

/--
[adeleDivisorDeg_add_single](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AdeleQuotientDim.lean)
-/
@[path]
lemma adeleDivisorDeg_add_single
  [Field F]
  [DecidableEq P]
  [HasResidueFieldSurjection P F k O]
  {D : P →₀ ℤ}
  {p : P} :
-- imply
  adeleDivisorDeg (F := F) (k := k) (O := O) (D + Finsupp.single p 1) = adeleDivisorDeg (F := F) (k := k) (O := O) D + (HasResidueFieldSurjection.degPlace (F := F) (k := k) (O := O) p : ℤ) := by
-- proof
  simp only [adeleDivisorDeg]
  rw [Finsupp.sum_add_index (fun a _ => by simp) (fun a _ n₁ n₂ => by ring)]
  rw [Finsupp.sum_single_index (by simp)]
  ring

/--
[adeleSpace_quotient_finrank_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AdeleQuotientDim.lean)
-/
@[path]
lemma adeleSpace_quotient_finrank_eq
  [Field F]
  [DecidableEq P]
  [HasResidueFieldSurjection P F k O]
  {A B : P →₀ ℤ}
-- given
  (hAB : ∀ p, A p ≤ B p) :
-- imply
  FiniteDimensional k (adeleSpace (F := F) (O := O) k (B : P → ℤ) ⧸ adeleComap k (A : P → ℤ) (B : P → ℤ)) ∧ (Module.finrank k (adeleSpace (F := F) (O := O) k (B : P → ℤ) ⧸ adeleComap k (A : P → ℤ) (B : P → ℤ)) : ℤ) = adeleDivisorDeg (F := F) (k := k) (O := O) (B - A) := by
-- proof
  induction h : divisorDistance A B using Nat.strongRecOn generalizing A B with
  | _ n ih =>
  by_cases h_eq : B - A = 0
  ·
    have hAeqB : (A : P → ℤ) = (B : P → ℤ) := by
      ext p
      have := Finsupp.ext_iff.mp h_eq p
      simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.coe_zero, Pi.zero_apply] at this
      omega
    rw [show adeleComap (F := F) (O := O) k (A : P → ℤ) (B : P → ℤ) = ⊤ from by
      rw [← hAeqB]; exact adeleComap_top_of_eq k _]
    rw [h_eq]
    refine ⟨inferInstance, ?_⟩
    simp only [adeleDivisorDeg, Finsupp.sum_zero_index]
    rw [finrank_quotient_top_eq_zero']
    simp
  ·
    obtain ⟨p₀, hp₀⟩ := Finsupp.support_nonempty_iff.mpr h_eq
    set B' : P →₀ ℤ := B - Finsupp.single p₀ 1 with hB'_def
    have hBA_pos : B p₀ - A p₀ ≥ 1 := by
      rw [Finsupp.mem_support_iff] at hp₀
      have h0 := hAB p₀
      have : (B - A) p₀ ≠ 0 := hp₀
      simp only [Finsupp.coe_sub, Pi.sub_apply] at this
      omega
    have hAB' : ∀ q, A q ≤ B' q := by
      intro q
      simp only [hB'_def, Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_apply]
      split_ifs with hq
      · subst hq; linarith [hBA_pos]
      · simp only [sub_zero]; exact hAB q
    have hB'B : ∀ q, B' q ≤ B q := by
      intro q
      simp only [hB'_def, Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_apply]
      split_ifs <;> linarith
    have hB'p₀ : B' p₀ = B p₀ - 1 := by
      simp [hB'_def, Finsupp.coe_sub, Pi.sub_apply]
    have hB_update : (B : P → ℤ) = Function.update (B' : P → ℤ) p₀ (B' p₀ + 1) := by
      funext q
      by_cases hq : q = p₀
      · subst hq; simp [Function.update, hB'p₀]
      · simp only [Function.update, dif_neg hq]
        simp only [hB'_def, Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_apply,
          if_neg (Ne.symm hq), sub_zero]
    have h_dist_lt : divisorDistance A B' < n := by
      rw [← h]; exact divisorDistance_sub_single_lt hAB h_eq hp₀
    have h_ind := ih _ h_dist_lt A B' hAB' rfl
    obtain ⟨hfd_ind, hrank_ind⟩ := h_ind
    have h_single := adeleSpace_singleStep_finrank (F := F) (O := O) k (B' : P → ℤ) p₀
    dsimp only at h_single
    rw [show Function.update (↑B' : P → ℤ) p₀ ((B' : P → ℤ) p₀ + 1) = (B : P → ℤ)
      from hB_update.symm] at h_single
    obtain ⟨h_single_fd, h_single_rank⟩ := h_single
    haveI := hfd_ind
    haveI := h_single_fd
    have h_chain := finrank_comap_chain
      (adeleSpace (F := F) (O := O) k (A : P → ℤ))
      (adeleSpace (F := F) (O := O) k (B' : P → ℤ))
      (adeleSpace (F := F) (O := O) k (B : P → ℤ))
      (adeleSpace_mono k hAB')
      (adeleSpace_mono k hB'B)
    obtain ⟨hfd_result, hrank_result⟩ := h_chain
    refine ⟨hfd_result, ?_⟩
    push_cast [hrank_result]
    rw [hrank_ind, h_single_rank]
    have h_BA : B - A = (B' - A) + Finsupp.single p₀ 1 := by
      ext q; simp [hB'_def]; ring
    rw [h_BA, adeleDivisorDeg_add_single]
end Lemma22_8


-- created on 2026-10-23

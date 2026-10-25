import Mathlib
import Def.ModularCurve_LevelOneProlongationPair
import Lemma.AlgebraicCurve.SemistableCharts
import Lemma.ModularCurve.SpecializeModuli
import Lemma.ModularCurve.SupersingularModuli
import Lemma.ModularCurve.SupersingularNodePlaces
import Structure.ModularCurve_LevelOneChartFst

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve

namespace ModularCurve.PlaceSpecialization.LevelOneProlongationPair

namespace ChartFst

theorem mapDomain_apply_eq_of_fibre {α β : Type*} (g : α → β) (D E : α →₀ ℤ) (b : β)
    (h : ∀ a, g a = b → D a = E a) : Finsupp.mapDomain g D b = Finsupp.mapDomain g E b := by
  classical
  have key : ∀ (G : α →₀ ℤ) (s : Finset α), G.support ⊆ s →
      Finsupp.mapDomain g G b = ∑ a ∈ s, if g a = b then G a else 0 := by
    intro G s hs
    rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum_of_support_subset G hs]
    · exact Finset.sum_congr rfl fun a _ => by rw [Finsupp.single_apply]
    · intro a _
      simp
  rw [key D (D.support ∪ E.support) Finset.subset_union_left,
    key E (D.support ∪ E.support) Finset.subset_union_right]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases hab : g a = b
  · rw [if_pos hab, if_pos hab, h a hab]
  · rw [if_neg hab, if_neg hab]

end ChartFst

variable {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  [CharP (ResidueField ↥A) p] [DecidableEq (ResidueField ↥A)]
  {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
  {P : PlaceSpecialization A p 1 data hKr (ResidueField ↥A) (IsLocalRing.residue ↥A) hα hβ}

namespace ChartFst

omit [DecidableEq (ResidueField ↥A)] in
theorem redBar_eq_id (R : LevelOneProlongationPair P) : R.redBar = RingHom.id _ := by
  refine RingHom.ext fun x => ?_
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  exact R.redBar_residue a

omit [DecidableEq (ResidueField ↥A)] in
theorem ι_coe_eq (R : LevelOneProlongationPair P) (x : ↥(modularFunctionFieldFullC (ResidueField ↥A) 1)) :
    ((R.ι x : ↥(modularFunctionFieldC (ResidueField ↥A) 1)) : LaurentSeries (ResidueField ↥A))
      = (x : LaurentSeries (ResidueField ↥A)) := by
  rw [R.ι_coe, redBar_eq_id, coeffMap_id]

omit [DecidableEq (ResidueField ↥A)] in
theorem ι_injective (R : LevelOneProlongationPair P) : Function.Injective R.ι := R.ι.injective

omit [DecidableEq (ResidueField ↥A)] in
theorem ι_surjective (R : LevelOneProlongationPair P) : Function.Surjective R.ι := by
  intro y
  refine ⟨⟨(y : LaurentSeries (ResidueField ↥A)), modularFunctionFieldC_le_full (ResidueField ↥A) 1 y.2⟩,
    Subtype.ext ?_⟩
  rw [ι_coe_eq]

omit [DecidableEq (ResidueField ↥A)] in
theorem ι_algebraMap (R : LevelOneProlongationPair P) (r : ResidueField ↥A) :
    R.ι (algebraMap (ResidueField ↥A) ↥(modularFunctionFieldFullC (ResidueField ↥A) 1) r)
      = algebraMap (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1) r := by
  apply Subtype.ext
  rw [ι_coe_eq]

  first
  | rw [IntermediateField.coe_algebraMap_apply, IntermediateField.coe_algebraMap_apply]
  | rw [Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap]
  | exact ((IsScalarTower.algebraMap_apply (ResidueField ↥A) ↥(modularFunctionFieldFullC (ResidueField ↥A) 1)
        (LaurentSeries (ResidueField ↥A)) r).symm.trans
      (IsScalarTower.algebraMap_apply (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1)
        (LaurentSeries (ResidueField ↥A)) r))

omit [DecidableEq (ResidueField ↥A)] in
theorem residue₁_ne_zero_iff (R : LevelOneProlongationPair P) (f : ↥R.R₁.integers) :
    R.residue₁ f ≠ 0 ↔ R.R₁.residue f ≠ 0 := by
  rw [residue₁_apply, Ne, map_eq_zero_iff _ (ChartFst.ι_injective R)]

end ChartFst

open Classical in


open Classical in


def chartFstDom (P : PlaceSpecialization A p 1 data hKr (ResidueField ↥A) (IsLocalRing.residue ↥A) hα hβ)
    (S₁ : Set (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)))) :
    Set (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) :=
  {W | P.IsStrictTypeOne W ∨ P.IsInftySide W ∨ W ∈ S₁}

omit [DecidableEq (ResidueField ↥A)] in
theorem mem_chartFstDom_iff (P : PlaceSpecialization A p 1 data hKr (ResidueField ↥A) (IsLocalRing.residue ↥A) hα hβ)
    (S₁ : Set (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))))
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) :
    W ∈ chartFstDom P S₁ ↔ P.IsStrictTypeOne W ∨ P.IsInftySide W ∨ W ∈ S₁ := Iff.rfl

section Chart

variable (R : LevelOneProlongationPair P)
  (S₁ : Set (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))))
  (Wn : Finset (Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1)))
  (hWn : ∀ w, w ∈ Wn ↔ w ∈ ssPlaces p 1 (ResidueField ↥A)) (Γ : R.ChartFstSupply S₁)

namespace ChartFstSupply

variable {R S₁}

theorem redFst_ne_charLGeomPlaceOfPoint_of_isCuspidal (Γ : R.ChartFstSupply S₁)
    {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))} (hW : P.IsCuspidal W)
    (a : ResidueField ↥A) : P.redFst W ≠ charLGeomPlaceOfPoint (ResidueField ↥A) a := by
  intro h
  obtain ⟨b, -, hb⟩ := (Γ.redFst_eq_charLGeomPlaceOfPoint_iff W a).mp h
  exact absurd (hW b) (not_le.mpr hb)

theorem frob_frob_charLGeomPlaceOfPoint_of_mem (Γ : R.ChartFstSupply S₁) {a : ResidueField ↥A}
    (ha : a ∈ ssJSet p (ResidueField ↥A)) :
    frobOnPlacesGeomLevel (ResidueField ↥A) 1 data hKr
        (frobOnPlacesGeomLevel (ResidueField ↥A) 1 data hKr (charLGeomPlaceOfPoint (ResidueField ↥A) a))
      = charLGeomPlaceOfPoint (ResidueField ↥A) a := by
  rw [Γ.frob_charLGeomPlaceOfPoint, Γ.frob_charLGeomPlaceOfPoint, ← pow_mul, ← sq, Γ.pow_sq_eq_self_of_mem a ha]

theorem exists_hasValue_of_mem_chartFstDom (Γ : R.ChartFstSupply S₁)
    {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))}
    (hW : W ∈ chartFstDom P S₁) (f : ↥(modularFunctionFieldBar (1 * p))) (hf : f ∈ R.R₁.integers)
    (hfib : ∀ w ∈ chartFstDom P S₁, P.redFst w = P.redFst W → f ∈ w.toValuationSubring) :
    ∃ c : ↥A, W.HasValue f (c : AlgebraicClosure ℚ) ∧
      (P.redFst W).HasValue (R.residue₁ ⟨f, hf⟩) (IsLocalRing.residue ↥A c) := by
  rcases hW with hW | hW | hW
  · exact Γ.pw_strict W hW f hf (fun w hw hwv => hfib w (Or.inl hw) hwv)
  · exact Γ.pw_cusp W hW f hf (fun w hw => hfib w (Or.inr (Or.inl hw))
      (by rw [Γ.redFst_eq_of_isInftySide w hw, Γ.redFst_eq_of_isInftySide W hW]))
  · exact Γ.sheet.pw_sheet W hW f hf (fun w hw hwv => hfib w (Or.inr (Or.inr hw)) hwv)

theorem mapDomain_redFst_eq_ord (Γ : R.ChartFstSupply S₁) (f : ↥R.R₁.integers) (hres : R.residue₁ f ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)))
    (hD : ∀ W ∈ chartFstDom P S₁, D W = W.ord (f : ↥(modularFunctionFieldBar (1 * p))))
    (hD0 : ∀ W, W ∉ chartFstDom P S₁ → D W = 0)
    (Q : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1))
    (hQ : Q ∉ ssPlaces p 1 (ResidueField ↥A)) :
    Finsupp.mapDomain P.redFst D Q = Q.ord (R.residue₁ f) := by
  classical
  have hres₁ : R.R₁.residue f ≠ 0 := (ChartFst.residue₁_ne_zero_iff R f).mp hres
  have hf0 : (f : ↥(modularFunctionFieldBar (1 * p))) ≠ 0 := by
    intro h
    apply hres₁
    have : f = 0 := Subtype.ext h
    rw [this, map_zero]
  obtain ⟨D', hD'⟩ := Γ.exists_divisor (f : ↥(modularFunctionFieldBar (1 * p))) hf0
  have hfib : ∀ (S : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) → Prop),
      (∀ W, P.redFst W = Q → (W ∈ chartFstDom P S₁ ↔ S W)) →
        Finsupp.mapDomain P.redFst D Q = Finsupp.mapDomain P.redFst (D'.filter S) Q := by
    intro S hS
    apply ChartFst.mapDomain_apply_eq_of_fibre
    intro W hW
    rw [Finsupp.filter_apply]
    by_cases hWd : W ∈ chartFstDom P S₁
    · rw [if_pos ((hS W hW).mp hWd), hD W hWd, hD' W]
    · rw [if_neg (fun h => hWd ((hS W hW).mpr h)), hD0 W hWd]
  have hcfix := Γ.cusp_fixed
  by_cases hfix : frobOnPlacesGeomLevel (ResidueField ↥A) 1 data hKr
      (frobOnPlacesGeomLevel (ResidueField ↥A) 1 data hKr Q) = Q
  · by_cases hc : Q = P.redFst (cuspInftyBar (1 * p))
    ·
      rw [hfib P.IsInftySide ?_]
      · rw [hc]
        convert Γ.div_cusp f.1 f.2 hres₁ D' hD'
      · intro W hW
        refine ⟨?_, fun h => Or.inr (Or.inl h)⟩
        rintro (h | h | h)
        · exact (h.2 ((hW.trans hc) ▸ hcfix)).elim
        · exact h
        · exact ((Γ.isAffineGeomPlace_iff _).mp (Γ.sheet.sheet_affine W h) (hW.trans hc)).elim
    ·
      rw [hfib (· ∈ S₁) ?_]
      · convert Γ.sheet.div_sheet f.1 f.2 hres₁ D' hD' Q hfix ((Γ.isAffineGeomPlace_iff Q).mpr hc) hQ
      · intro W hW
        refine ⟨?_, fun h => Or.inr (Or.inr h)⟩
        rintro (h | h | h)
        · exact (h.2 (hW ▸ hfix)).elim
        · exact absurd ((Γ.redFst_eq_of_isInftySide W h).symm.trans hW) (Ne.symm hc)
        · exact h
  ·
    rw [hfib P.IsStrictTypeOne ?_]
    · convert Γ.div_strict f.1 f.2 hres₁ D' hD' Q hfix
    · intro W hW
      refine ⟨?_, fun h => Or.inl h⟩
      rintro (h | h | h)
      · exact h
      · exact (hfix (((Γ.redFst_eq_of_isInftySide W h).symm.trans hW) ▸ hcfix)).elim
      · exact (hfix (hW ▸ Γ.sheet.sheet_fixed W h)).elim

end ChartFstSupply

def chartFst : ComponentChart A ↥(modularFunctionFieldBar (1 * p)) ↥(modularFunctionFieldC (ResidueField ↥A) 1) where
  integers := R.R₁.integers
  residue := R.residue₁
  dom := chartFstDom P S₁
  nodes := Wn
  placeMap := P.redFst
  algebraMap_mem_iff := R.R₁.algebraMap_mem_iff
  residue_surjective := (ChartFst.ι_surjective R).comp R.R₁.residue_surjective
  ker_residue := by
    rw [← R.R₁.ker_residue]
    ext x
    simp only [RingHom.mem_ker, residue₁_apply, map_eq_zero_iff _ (ChartFst.ι_injective R)]
  residue_algebraMap := fun a => by
    rw [residue₁_apply, R.R₁.residue_algebraMap, ChartFst.ι_algebraMap]
  exists_smul_mem := fun f hf => by
    obtain ⟨c, h, hres⟩ := R.R₁.exists_smul_mem f hf
    exact ⟨c, h, (ChartFst.residue₁_ne_zero_iff R ⟨_, h⟩).mpr hres⟩
  placeMap_not_mem_nodes := fun W hW hn => by
    have hss : P.redFst W ∈ ssPlaces p 1 (ResidueField ↥A) := (hWn _).mp hn
    obtain ⟨a, ha, hWa⟩ := (Γ.mem_ssPlaces_iff _).mp hss
    rcases hW with h | h | h
    · exact h.2 (hWa ▸ Γ.frob_frob_charLGeomPlaceOfPoint_of_mem ha)
    · exact Γ.redFst_ne_charLGeomPlaceOfPoint_of_isCuspidal h.1 a hWa.symm
    · exact Γ.sheet.sheet_not_mem_ssPlaces W h hss
  pointwise := fun W hW _ f hf hfib => by
    obtain ⟨c, hc, hv⟩ := Γ.exists_hasValue_of_mem_chartFstDom hW f hf hfib
    have hev : W.evalAt f = (c : AlgebraicClosure ℚ) := by
      rw [W.evalAt_of_mem hc.mem, hc.residue_eq, Place.residueInv_algebraMap]
    have hcA : W.evalAt f ∈ A := hev ▸ c.2
    refine ⟨hv.mem, hcA, ?_⟩
    have : (⟨W.evalAt f, hcA⟩ : ↥A) = c := Subtype.ext hev
    rw [this]
    exact hv.residue_eq.symm
  mapDomain_placeMap := fun f hres D hD hD0 Q hQ =>
    Γ.mapDomain_redFst_eq_ord f hres D hD hD0 Q (fun h => hQ ((hWn Q).mpr h))

@[simp] theorem chartFst_integers : (chartFst R S₁ Wn hWn Γ).integers = R.R₁.integers := rfl
@[simp] theorem chartFst_residue : (chartFst R S₁ Wn hWn Γ).residue = R.residue₁ := rfl
@[simp] theorem chartFst_dom : (chartFst R S₁ Wn hWn Γ).dom = chartFstDom P S₁ := rfl
@[simp] theorem chartFst_nodes : (chartFst R S₁ Wn hWn Γ).nodes = Wn := rfl
@[simp] theorem chartFst_placeMap : (chartFst R S₁ Wn hWn Γ).placeMap = P.redFst := rfl

theorem chartFst_residue_eq_modularRedLocHom (f : ↥(modularFunctionFieldBar (1 * p)))
    (hf : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * p) A.toSubring (IsLocalRing.residue ↥A)) :
    ∃ h : f ∈ (chartFst R S₁ Wn hWn Γ).integers,
      (((chartFst R S₁ Wn hWn Γ).residue ⟨f, h⟩ : ↥(modularFunctionFieldC (ResidueField ↥A) 1)) :
          LaurentSeries (ResidueField ↥A)) =
        CharPReduction.modularRedLocHom (1 * p) A.toSubring (IsLocalRing.residue ↥A) ⟨_, hf⟩ :=
  R.residue₁_eq_modularRedLocHom f hf

theorem chartFst_residue_coeffMap (y : LaurentSeries ↥A)
    (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar (1 * p)) :
    ∃ hint : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar (1 * p))) ∈ (chartFst R S₁ Wn hWn Γ).integers,
      (((chartFst R S₁ Wn hWn Γ).residue ⟨_, hint⟩ : ↥(modularFunctionFieldC (ResidueField ↥A) 1)) :
          LaurentSeries (ResidueField ↥A)) = coeffMap (IsLocalRing.residue ↥A) y := by
  obtain ⟨h, hres⟩ := R.residue₁_coeffMap y hy
  exact ⟨h, (ChartFst.ι_coe_eq R _).trans hres⟩

theorem mem_chartFst_nodes_iff (x : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1)) :
    x ∈ (chartFst R S₁ Wn hWn Γ).nodes ↔
      ∃ a ∈ ssJSet p (ResidueField ↥A), charLGeomPlaceOfPoint (ResidueField ↥A) a = x := by
  rw [chartFst_nodes, hWn, Γ.mem_ssPlaces_iff]

theorem mem_chartFst_dom_iff (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) :
    W ∈ (chartFst R S₁ Wn hWn Γ).dom ↔ P.IsStrictTypeOne W ∨ P.IsInftySide W ∨ W ∈ S₁ := Iff.rfl

theorem cuspInftyBar_mem_chartFst_dom : cuspInftyBar (1 * p) ∈ (chartFst R S₁ Wn hWn Γ).dom :=
  Or.inr (Or.inl Γ.isInftySide_cuspInftyBar)

def IsSSCentred (A : ValuationSubring (AlgebraicClosure ℚ)) (p : ℕ) [Fact p.Prime]
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) (a : ResidueField ↥A) : Prop :=
  (∃ x : ↥A, IsLocalRing.residue ↥A x = a ∧
      0 < W.ord (PlaceSpecialization.jFun (q := p) -
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (x : AlgebraicClosure ℚ))) ∧
  (∃ y : ↥A, IsLocalRing.residue ↥A y = a ^ p ∧
      0 < W.ord (PlaceSpecialization.jqFun (q := p) -
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (y : AlgebraicClosure ℚ)))

theorem isSSCentred_iff (A : ValuationSubring (AlgebraicClosure ℚ)) (p : ℕ) [Fact p.Prime]
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) (a : ResidueField ↥A) :
    IsSSCentred A p W a ↔
      (∃ x : ↥A, IsLocalRing.residue ↥A x = a ∧
        0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * p) (jq_mem (1 * p)))⟩ : ↥(modularFunctionFieldBar (1 * p))) -
            algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (x : AlgebraicClosure ℚ))) ∧
      (∃ y : ↥A, IsLocalRing.residue ↥A y = a ^ p ∧
        0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * p) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * p) (dvd_refl (1 * p)))⟩ : ↥(modularFunctionFieldBar (1 * p))) -
            algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (y : AlgebraicClosure ℚ))) :=
  Iff.rfl

theorem not_isSSCentred_of_mem_chartFst_dom (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)))
    (hW : W ∈ (chartFst R S₁ Wn hWn Γ).dom) (a : ResidueField ↥A) (ha : a ∈ ssJSet p (ResidueField ↥A)) :
    ¬ IsSSCentred A p W a := by
  rintro ⟨⟨x, hx, hxW⟩, -⟩
  have hred : P.redFst W = charLGeomPlaceOfPoint (ResidueField ↥A) a :=
    (Γ.redFst_eq_charLGeomPlaceOfPoint_iff W a).mpr ⟨x, hx, hxW⟩
  exact (chartFst R S₁ Wn hWn Γ).placeMap_not_mem_nodes W hW
    ((hWn _).mpr ((Γ.mem_ssPlaces_iff _).mpr ⟨a, ha, hred.symm⟩))

theorem redFst_eq_redFst_cuspInftyBar_iff_of_mem_chartFst_dom
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) (hW : W ∈ (chartFst R S₁ Wn hWn Γ).dom) :
    P.redFst W = P.redFst (cuspInftyBar (1 * p)) ↔ P.IsInftySide W := by
  refine ⟨fun h => ?_, Γ.redFst_eq_of_isInftySide W⟩
  rcases hW with hW | hW | hW
  · exact (hW.2 (h ▸ Γ.cusp_fixed)).elim
  · exact hW
  · exact ((Γ.isAffineGeomPlace_iff _).mp (Γ.sheet.sheet_affine W hW) h).elim

theorem isStrictTypeOne_iff_of_mem_chartFst_dom
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) (hW : W ∈ (chartFst R S₁ Wn hWn Γ).dom) :
    P.IsStrictTypeOne W ↔ frobOnPlacesGeomLevel (ResidueField ↥A) 1 data hKr
      (frobOnPlacesGeomLevel (ResidueField ↥A) 1 data hKr (P.redFst W)) ≠ P.redFst W := by
  refine ⟨fun h => h.2, fun h => ?_⟩
  rcases hW with hW | hW | hW
  · exact hW
  · exact (h ((Γ.redFst_eq_of_isInftySide W hW) ▸ Γ.cusp_fixed)).elim
  · exact (h (Γ.sheet.sheet_fixed W hW)).elim

end Chart

end ModularCurve.PlaceSpecialization.LevelOneProlongationPair

end

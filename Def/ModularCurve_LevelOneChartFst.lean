import Mathlib
import Def.ModularCurve_LevelOneProlongationPair
import Def.AlgebraicCurve_SemistableCharts
import Def.ModularCurve_SpecializeModuli
import Lemma.WeierstrassCurve.SupersingularModuli
import Def.ModularCurve_SupersingularNodePlaces
import Structure.ModularCurve_LevelOneChartFst

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve ValuationSubring Finsupp WeierstrassCurve Finset

namespace ModularCurve.PlaceSpecialization.LevelOneProlongationPair


variable {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  [CharP (ResidueField ↥A) p] [DecidableEq (ResidueField ↥A)]
  {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
  {P : PlaceSpecialization A p 1 data hKr (ResidueField ↥A) (IsLocalRing.residue ↥A) hα hβ}

namespace ChartFst

omit [DecidableEq (ResidueField ↥A)] in
end ChartFst

open Classical in


open Classical in


def chartFstDom (P : PlaceSpecialization A p 1 data hKr (ResidueField ↥A) (IsLocalRing.residue ↥A) hα hβ)
    (S₁ : Set (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)))) :
    Set (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) :=
  {W | P.IsStrictTypeOne W ∨ P.IsInftySide W ∨ W ∈ S₁}

omit [DecidableEq (ResidueField ↥A)] in
section Chart

variable (R : LevelOneProlongationPair P)
  (S₁ : Set (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))))
  (Wn : Finset (Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1)))
  (hWn : ∀ w, w ∈ Wn ↔ w ∈ ssPlaces p 1 (ResidueField ↥A)) (Γ : R.ChartFstSupply S₁)


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

def IsSSCentred (A : ValuationSubring (AlgebraicClosure ℚ)) (p : ℕ) [Fact p.Prime]
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) (a : ResidueField ↥A) : Prop :=
  (∃ x : ↥A, IsLocalRing.residue ↥A x = a ∧
      0 < W.ord (PlaceSpecialization.jFun (q := p) -
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (x : AlgebraicClosure ℚ))) ∧
  (∃ y : ↥A, IsLocalRing.residue ↥A y = a ^ p ∧
      0 < W.ord (PlaceSpecialization.jqFun (q := p) -
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (y : AlgebraicClosure ℚ)))

end Chart

end ModularCurve.PlaceSpecialization.LevelOneProlongationPair

end

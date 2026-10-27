import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonSubdivisionIndexGeometry.Part3
open StatMech StatMech.FrontierD


/--
[finSigmaFinEquiv_fkRectFinSigmaSucc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonSubdivisionIndexGeometry.lean)
-/
@[path]
private lemma finSigmaFinEquiv_fkRectFinSigmaSucc_eq
  {n : ℕ}
  {scale : Fin n → ℕ}
  [NeZero (∑ i, scale i)]
  {z : Σ i, Fin (scale i)}
-- given
  (hscale : ∀ i, 0 < scale i) :
-- imply
  finSigmaFinEquiv (fkRectFinSigmaSucc scale hscale z) = finSigmaFinEquiv z + 1 := by
-- proof
  apply StatMech.FrontierD.finSigmaFinEquiv_fkRectFinSigmaSucc scale hscale z

/--
[fkRectBlackOrbitRibbonSubdivisionWord_length_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonSubdivisionIndexGeometry.lean)
-/
@[path]
private lemma fkRectBlackOrbitRibbonSubdivisionWord_length_eq_sum_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  (fkRectBlackOrbitRibbonSubdivisionWord R omega d).length = ∑ k : Fin (fkRectBlackOrbitMedialRibbonWord R omega d).length, onsAnisotropicStepScale (8 * R.medialTorus.width) (8 * R.medialTorus.height) (fkRectBlackOrbitMedialRibbonFlatDirection R omega d k) := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitRibbonSubdivisionWord_length_eq_sum R omega d

/--
[fkRectBlackOrbitRibbonSubdivisionIndexEquiv_symm_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonSubdivisionIndexGeometry.lean)
-/
@[path]
private lemma fkRectBlackOrbitRibbonSubdivisionIndexEquiv_symm_val_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus}
  {z : FKRectBlackOrbitRibbonSubdivisionIndex R omega d} :
-- imply
  ((fkRectBlackOrbitRibbonSubdivisionIndexEquiv R omega d).symm z).val = (finSigmaFinEquiv z).val := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitRibbonSubdivisionIndexEquiv_symm_val R omega d z

/--
[fkRectBlackOrbitRibbonSubdivisionIndexEquiv_symm_val_cast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonSubdivisionIndexGeometry.lean)
-/
@[path]
private lemma fkRectBlackOrbitRibbonSubdivisionIndexEquiv_symm_val_cast_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus}
  {scale : Fin (fkRectBlackOrbitMedialRibbonWord R omega d).length → ℕ}
  {i : Fin (fkRectBlackOrbitMedialRibbonWord R omega d).length}
  {r : Fin (onsAnisotropicStepScale (8 * R.medialTorus.width) (8 * R.medialTorus.height) (fkRectBlackOrbitMedialRibbonFlatDirection R omega d i))}
-- given
  (hscale : scale = fun i => onsAnisotropicStepScale (8 * R.medialTorus.width) (8 * R.medialTorus.height) (fkRectBlackOrbitMedialRibbonFlatDirection R omega d i)) :
-- imply
  let r0 : Fin (scale i) := Fin.cast (congrFun hscale i).symm r ((fkRectBlackOrbitRibbonSubdivisionIndexEquiv R omega d).symm ⟨i, r⟩).val = (finSigmaFinEquiv (⟨i, r0⟩ : Σ j, Fin (scale j))).val := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitRibbonSubdivisionIndexEquiv_symm_val_cast R omega d scale hscale i r

/--
[fkRectBlackOrbitRibbonSubdivisionStepScale_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonSubdivisionIndexGeometry.lean)
-/
@[path]
private lemma fkRectBlackOrbitRibbonSubdivisionStepScale_pos_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus}
  {k : Fin (fkRectBlackOrbitMedialRibbonWord R omega d).length} :
-- imply
  0 < onsAnisotropicStepScale (8 * R.medialTorus.width) (8 * R.medialTorus.height) (fkRectBlackOrbitMedialRibbonFlatDirection R omega d k) := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitRibbonSubdivisionStepScale_pos R omega d k

/--
[fkRectBlackOrbitRibbonSubdivisionDirection_nonUturn_index](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonSubdivisionIndexGeometry.lean)
-/
@[path]
private lemma fkRectBlackOrbitRibbonSubdivisionDirection_nonUturn_index_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus}
  {z : FKRectBlackOrbitRibbonSubdivisionIndex R omega d} :
-- imply
  fkRectBlackOrbitMedialRibbonFlatDirection R omega d (fkRectFinSigmaSucc (fun i => onsAnisotropicStepScale (8 * R.medialTorus.width) (8 * R.medialTorus.height) (fkRectBlackOrbitMedialRibbonFlatDirection R omega d i)) (fkRectBlackOrbitRibbonSubdivisionStepScale_pos R omega d) z).1 ≠ fkRectBlackOrbitMedialRibbonFlatDirection R omega d z.1 + 2 := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitRibbonSubdivisionDirection_nonUturn_index R omega d z

/--
[fkRectBlackOrbitRibbonSubdivisionIndexEquiv_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonSubdivisionIndexGeometry.lean)
-/
@[path]
private lemma fkRectBlackOrbitRibbonSubdivisionIndexEquiv_add_one_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus}
  {k : Fin (fkRectBlackOrbitRibbonSubdivisionWord R omega d).length} :
-- imply
  fkRectBlackOrbitRibbonSubdivisionIndexEquiv R omega d (k + 1) = fkRectFinSigmaSucc (fun i => onsAnisotropicStepScale (8 * R.medialTorus.width) (8 * R.medialTorus.height) (fkRectBlackOrbitMedialRibbonFlatDirection R omega d i)) (fkRectBlackOrbitRibbonSubdivisionStepScale_pos R omega d) (fkRectBlackOrbitRibbonSubdivisionIndexEquiv R omega d k) := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitRibbonSubdivisionIndexEquiv_add_one R omega d k

/--
[fkRectBlackOrbitRibbonSubdivisionSide_eq_refinedProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonSubdivisionIndexGeometry.lean)
-/
@[path]
private lemma fkRectBlackOrbitRibbonSubdivisionSide_eq_refinedProduct_eq
  {R : FKRectTorus} :
-- imply
  (8 * R.medialTorus.width) * (8 * R.medialTorus.height) = fkRectBlackOrbitRibbonSubdivisionSide R := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitRibbonSubdivisionSide_eq_refinedProduct R

/--
[fkRectBlackOrbitRibbonSubdivisionSite_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonSubdivisionIndexGeometry.lean)
-/
@[path]
private lemma fkRectBlackOrbitRibbonSubdivisionSite_injective_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  Function.Injective (fkRectBlackOrbitRibbonSubdivisionSite R omega d) := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitRibbonSubdivisionSite_injective R omega d


-- created on 2026-10-23

import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicTopologyI.code.Section24
open CategoryTheory MonoidalCategory Limits UniversalCoefficientTheorem


namespace UniversalCoefficientTheorem

/--
[homologyπ_comp_uctAlpha](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section24.lean)
-/
@[path]
cycles to homology recovers the basic `cyclesToHomologyTC` map. This is the universal
property of the cokernel description of homology. -/
@[reassoc (attr := simp)]
lemma homologyπ_comp_uctAlpha (R : Type*) [CommRing R] [IsPrincipalIdealRing R]
  (M : ModuleCat R) (n : ℕ) (C : ChainComplex (ModuleCat R) ℕ)
  (hfree : ∀ i, Module.Free R (C.X i)) :
  ((tensoringRight (ModuleCat R)).obj M).map (C.homologyπ (n + 1)) ≫
    uctAlpha R M n C hfree = cyclesToHomologyTC R M n C := by
  have := (Cofork.IsColimit.desc'
    (isColimitCoforkMapOfIsColimit' ((tensoringRight (ModuleCat R)).obj M)
      (C.toCycles_comp_homologyπ (n + 2) (n + 1))
      (C.homologyIsCokernel (n + 2) (n + 1) (down_prev_succ n)))
    (cyclesToHomologyTC R M n C)
    (by rw [toCycles_comp_cyclesToHomologyTC, zero_comp])).2
  simp only [CokernelCofork.π_ofπ] at this
  exact this
set_option maxHeartbeats 800000 in

end UniversalCoefficientTheorem

namespace UniversalCoefficientTheorem

/--
[uctAlpha_natural](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section24.lean)
-/
@[path]
lemma uctAlpha_natural
  {R : Type*}
  [CommRing R]
  [IsPrincipalIdealRing R]
  {M : ModuleCat R}
  {n : ℕ}
  {C D : ChainComplex (ModuleCat R) ℕ}
  {φ : C ⟶ D}
-- given
  (hfreeC : ∀ i, Module.Free R (C.X i))
  (hfreeD : ∀ i, Module.Free R (D.X i)) :
-- imply
  uctAlpha R M n C hfreeC ≫ HomologicalComplex.homologyMap (tensorComplexMap R φ M) (n + 1) = ((tensoringRight (ModuleCat R)).obj M).map (HomologicalComplex.homologyMap φ (n + 1)) ≫ uctAlpha R M n D hfreeD := by
-- proof
  have hcokerFC := isColimitCoforkMapOfIsColimit' ((tensoringRight (ModuleCat R)).obj M)
    (C.toCycles_comp_homologyπ (n + 2) (n + 1))
    (C.homologyIsCokernel (n + 2) (n + 1) (down_prev_succ n))
  apply Cofork.IsColimit.hom_ext hcokerFC
  simp only [CokernelCofork.π_ofπ]
  erw [homologyπ_comp_uctAlpha_assoc,
    ← ((tensoringRight (ModuleCat R)).obj M).map_comp_assoc,
    HomologicalComplex.homologyπ_naturality,
    ((tensoringRight (ModuleCat R)).obj M).map_comp_assoc,
    homologyπ_comp_uctAlpha]
  simp only [cyclesToHomologyTC, Category.assoc, HomologicalComplex.homologyπ_naturality]
  rw [HomologicalComplex.liftCycles_comp_cyclesMap_assoc,
    HomologicalComplex.comp_liftCycles_assoc]
  congr 2
  change ((tensoringRight (ModuleCat R)).obj M).map (C.iCycles (n + 1)) ≫
    ((tensoringRight (ModuleCat R)).obj M).map (φ.f (n + 1)) =
    ((tensoringRight (ModuleCat R)).obj M).map (HomologicalComplex.cyclesMap φ (n + 1)) ≫
      ((tensoringRight (ModuleCat R)).obj M).map (D.iCycles (n + 1))
  rw [← ((tensoringRight (ModuleCat R)).obj M).map_comp,
    ← ((tensoringRight (ModuleCat R)).obj M).map_comp,
    HomologicalComplex.cyclesMap_i]

end UniversalCoefficientTheorem

namespace UniversalCoefficientTheorem

/--
[cyclesToHomologyTC_naturality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section24.lean)
-/
@[path]
lemma cyclesToHomologyTC_naturality
  {R : Type*}
  [CommRing R]
  {M₁ M₂ : ModuleCat R}
  {f : M₁ ⟶ M₂}
  {n : ℕ}
  {C : ChainComplex (ModuleCat R) ℕ} :
-- imply
  ((tensoringRight (ModuleCat R)).map f).app (C.cycles (n + 1)) ≫ cyclesToHomologyTC R M₂ n C = cyclesToHomologyTC R M₁ n C ≫ HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex ((tensoringRight (ModuleCat R)).map f) (ComplexShape.down ℕ)).app C) (n + 1) := by
-- proof
  simp only [cyclesToHomologyTC, Category.assoc]
  erw [HomologicalComplex.homologyπ_naturality]
  rw [HomologicalComplex.liftCycles_comp_cyclesMap_assoc,
    HomologicalComplex.comp_liftCycles_assoc]
  congr 2
  exact (((tensoringRight (ModuleCat R)).map f).naturality (C.iCycles (n + 1))).symm
set_option maxHeartbeats 800000 in
/-- The composition $\beta \circ \alpha = 0$, i.e. the maps in the UCT short complex
form a complex. -/

end UniversalCoefficientTheorem

/--
[down_next_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section24.lean)
-/
@[path]
private lemma down_next_succ_eq
  {n : ℕ} :
-- imply
  (ComplexShape.down ℕ).next (n + 1) = n := by
-- proof
  apply UniversalCoefficientTheorem.down_next_succ n

/--
[down_prev_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section24.lean)
-/
@[path]
private lemma down_prev_succ_eq
  {n : ℕ} :
-- imply
  (ComplexShape.down ℕ).prev (n + 1) = n + 2 := by
-- proof
  apply UniversalCoefficientTheorem.down_prev_succ n

/--
[iCycles_tensor_comp_d](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section24.lean)
-/
@[path]
private lemma iCycles_tensor_comp_d_eq
  {R : Type*}
  [CommRing R]
  {M : ModuleCat R}
  {n : ℕ}
  {C : ChainComplex (ModuleCat R) ℕ} :
-- imply
  ((tensoringRight (ModuleCat R)).obj M).map (C.iCycles (n + 1)) ≫ (tensorComplex R C M).d (n + 1) n = 0 := by
-- proof
  apply UniversalCoefficientTheorem.iCycles_tensor_comp_d R M n C

/--
[toCycles_comp_cyclesToHomologyTC](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section24.lean)
-/
@[path]
private lemma toCycles_comp_cyclesToHomologyTC_eq
  {R : Type*}
  [CommRing R]
  {M : ModuleCat R}
  {n : ℕ}
  {C : ChainComplex (ModuleCat R) ℕ} :
-- imply
  ((tensoringRight (ModuleCat R)).obj M).map (C.toCycles (n + 2) (n + 1)) ≫ cyclesToHomologyTC R M n C = 0 := by
-- proof
  apply UniversalCoefficientTheorem.toCycles_comp_cyclesToHomologyTC R M n C

/--
[homology](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section24.lean)
-/
@[path]
private lemma homology_eq
  {R : Type*}
  [CommRing R]
  [IsPrincipalIdealRing R]
  {M : ModuleCat R}
  {n : ℕ}
  {C : ChainComplex (ModuleCat R) ℕ}
-- given
  (hfree : ∀ i, Module.Free R (C.X i)) :
-- imply
  ((tensoringRight (ModuleCat R)).obj M).map (C.homologyπ (n + 1)) ≫ uctAlpha R M n C hfree = cyclesToHomologyTC R M n C := by
-- proof
  apply UniversalCoefficientTheorem.homology R M n C hfree

/--
[res_d_comp_pi_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section24.lean)
-/
@[path]
private lemma res_d_comp_pi_zero_eq
  {R : Type*}
  [CommRing R]
  {M : ModuleCat R}
  {P : ProjectiveResolution M} :
-- imply
  P.complex.d 1 0 ≫ P.π.f 0 = 0 := by
-- proof
  apply UniversalCoefficientTheorem.res_d_comp_pi_zero R M P


-- created on 2026-10-23

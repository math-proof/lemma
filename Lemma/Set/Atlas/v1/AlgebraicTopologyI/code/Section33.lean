import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicTopologyI.code.Section33.Part2
open CategoryTheory AlgebraicTopology Limits SingularCohomology in
open SingularCohomology


/--
[SingularCohomology.kroneckerPairing_natural](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section33.lean)
-/
@[path]
lemma SingularCohomology.kroneckerPairing_natural
  {R : Type}
  [CommRing R]
  {X Y : TopCat.{0}}
  {f : X ⟶ Y}
  {p : ℕ}
  {b : (SingularCohomology.singularCohomologyR R Y p : Type)}
  {x : (SingularCohomology.singularHomologyModule R X p : Type)} :
-- imply
  SingularCohomology.kroneckerPairing R X p (SingularCohomology.cohomologyPullback R X Y f p b) x = SingularCohomology.kroneckerPairing R Y p b (SingularCohomology.homologyPushforward R X Y f p x) := by
-- proof
  set SccX := ((singularChainCx R X).linearYonedaObj R (ModuleCat.of R R)).sc p
  set SccY := ((singularChainCx R Y).linearYonedaObj R (ModuleCat.of R R)).sc p
  set ScX := (singularChainCx R X).sc p
  set ScY := (singularChainCx R Y).sc p
  set φcc := (HomologicalComplex.shortComplexFunctor (ModuleCat.{0} R) (ComplexShape.up ℕ) p).map
    (cochainPullbackMap R X Y f)
  set γcc : ShortComplex.LeftHomologyMapData φcc SccY.moduleCatLeftHomologyData
    SccX.moduleCatLeftHomologyData := default
  set chainMapF := ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map f
  set φc := (HomologicalComplex.shortComplexFunctor (ModuleCat.{0} R) (ComplexShape.down ℕ) p).map
    chainMapF
  set γc : ShortComplex.LeftHomologyMapData φc ScX.moduleCatLeftHomologyData
    ScY.moduleCatLeftHomologyData := default
  have hcc : SccX.moduleCatHomologyIso.hom.hom
    (ShortComplex.homologyMap φcc b) = γcc.φH.hom (SccY.moduleCatHomologyIso.hom.hom b) :=
    congr_arg (·.hom b) γcc.homologyMap_comm
  have hc : ScY.moduleCatHomologyIso.hom.hom
    (ShortComplex.homologyMap φc x) = γc.φH.hom (ScX.moduleCatHomologyIso.hom.hom x) :=
    congr_arg (·.hom x) γc.homologyMap_comm
  simp only [kroneckerPairing, cohomologyPullback, homologyPushforward,
    HomologicalComplex.homologyFunctor_map,
    LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply]
  erw [hcc, hc]
  refine Submodule.Quotient.induction_on _
    (SccY.moduleCatHomologyIso.hom.hom b) (fun β => ?_)
  refine Submodule.Quotient.induction_on _
    (ScX.moduleCatHomologyIso.hom.hom x) (fun ξ => ?_)
  have hccpi : γcc.φH.hom (Submodule.Quotient.mk β) =
    Submodule.Quotient.mk (γcc.φK.hom β) :=
    congr_arg (·.hom β) γcc.commπ
  have hcpi : γc.φH.hom (Submodule.Quotient.mk ξ) =
    Submodule.Quotient.mk (γc.φK.hom ξ) :=
    congr_arg (·.hom ξ) γc.commπ
  rw [hccpi, hcpi]
  simp only [Submodule.liftQ_apply, LinearMap.coe_mk, AddHom.coe_mk]
  rfl

/--
[SingularCohomology.kroneckerPairing_prodIsoProd_compat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section33.lean)
-/
@[path]
lemma SingularCohomology.kroneckerPairing_prodIsoProd_compat
  {R : Type}
  [CommRing R]
  {X Y : TopCat.{0}}
  {n : ℕ}
  {c : ↑(singularCohomology R (X ⨯ Y) (ModuleCat.of R R) n)}
-- given
  (h : ↑(SingularCohomology.singularHomologyModule R (TopCat.of (↑X × ↑Y)) n)) :
-- imply
  SingularCohomology.kroneckerPairing R (TopCat.of (↑X × ↑Y)) n ((singularCohomologyMap R (TopCat.prodIsoProd X Y).inv n).hom c) h = SingularCohomology.kroneckerPairing R (X ⨯ Y) n c ((SingularCohomology.homologyPushforward R (TopCat.of (↑X × ↑Y)) (X ⨯ Y) (TopCat.prodIsoProd X Y).inv n).hom h) :=
-- proof
  SingularCohomology.kroneckerPairing_natural R (TopCat.of (↑X × ↑Y)) (X ⨯ Y)
    (TopCat.prodIsoProd X Y).inv n c h
/-- Cochain-level form of **Lemma 33.2**: the Kronecker pairing of the
Alexander–Whitney cup product cohomology cross product with the pushforward of
a homology cross product equals $(-1)^{pq}$ times the product of the individual
Kronecker pairings. -/

/--
[down_prev_eq_up_next](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section33.lean)
-/
@[path]
private lemma down_prev_eq_up_next_eq
  {p : ℕ} :
-- imply
  (ComplexShape.down ℕ).prev p = (ComplexShape.up ℕ).next p := by
-- proof
  apply down_prev_eq_up_next p

/--
[down_next_eq_up_prev](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section33.lean)
-/
@[path]
private lemma down_next_eq_up_prev_eq
  {p : ℕ} :
-- imply
  (ComplexShape.down ℕ).next p = (ComplexShape.up ℕ).prev p := by
-- proof
  apply down_next_eq_up_prev p


-- created on 2026-10-23

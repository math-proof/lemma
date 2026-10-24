/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/GradedAlgebra/MultigradedPoincareFiniteSupport.lean -/


import sympy.atlas.RingTheory.GradedAlgebra.MultigradedPoincareFiniteSupport
import Lemma.Int.GradedAlgebra.MultigradedPoincareFiniteSupport


open scoped DirectSum
open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace MetaMathlibExtTest

private abbrev K : Type := Rat
private abbrev n : ℕ := 0
private abbrev R : Type := MvPolynomial (Fin n) K
private abbrev M : Type := PUnit
private abbrev Z : ModuleCat R := ModuleCat.of R M

private theorem hZeroObj : IsZero Z :=
  ModuleCat.isZero_of_subsingleton Z

private instance projZ : Projective Z :=
  hZeroObj.projective

private abbrev resolution : ProjectiveResolution Z :=
  ProjectiveResolution.self Z

private abbrev ι : ℕ → Type := fun _ => Empty

private def trivialGrading {X : Type} [AddCommGroup X] [Module R X] [Module K X]
    [Subsingleton X] : MetaMathlibExt.MultigradedPolynomialModule K 0 X where
  component := fun _ => ⊥
  decomposition :=
    { decompose' := fun _ => 0
      left_inv := fun x => Subsingleton.elim _ _
      right_inv := fun x => Subsingleton.elim _ _ }
  smul_via_C := fun k m => Subsingleton.elim _ _
  monomial_mem := by
    intro a c α m _
    change _ = 0
    exact Subsingleton.elim _ _

private def targetGraded : MetaMathlibExt.MultigradedPolynomialModule K n M :=
  trivialGrading

private theorem termSubsingleton (i : ℕ) :
    Subsingleton ↥(resolution.complex.X i) := by
  apply ModuleCat.isZero_iff_subsingleton.mp
  rw [resolution, ProjectiveResolution.self_complex]
  exact (HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) i).map_isZero
    ((ChainComplex.single₀ (ModuleCat R)).map_isZero hZeroObj)

private def termFreeModule (i : ℕ) :
    letI : Module K ↥(resolution.complex.X i) :=
      Module.compHom _ (MvPolynomial.C : K →+* R);
    MetaMathlibExt.MultigradedFreeModule K n ↥(resolution.complex.X i) (ι i) := by
  haveI := termSubsingleton i
  letI : Module K ↥(resolution.complex.X i) :=
    Module.compHom _ (MvPolynomial.C : K →+* R)
  exact
    { graded := trivialGrading
      basis := Module.Basis.empty _
      degree := fun j => j.elim
      basis_mem := fun j => j.elim }

private def resFree :
    MetaMathlibExt.MultigradedFreeResolution K n M targetGraded resolution ι where
  termFree := fun i => termFreeModule i
  diffDegreeZero := by
    intro i alpha m hm
    have _hNext : Subsingleton ↥(resolution.complex.X (i + 1)) :=
      termSubsingleton (i + 1)
    have _hCurr : Subsingleton ↥(resolution.complex.X i) := termSubsingleton i
    change _ = 0
    exact Subsingleton.elim _ _
  augDegreeZero := by
    intro alpha m hm
    have _hTerm : Subsingleton ↥(resolution.complex.X 0) := termSubsingleton 0
    change _ = 0
    exact Subsingleton.elim _ _

private theorem baseZero (i : ℕ) :
    IsZero ((MetaMathlibExt.baseChangedComplex resolution).X i) := by
  let _alg : Algebra R K := MetaMathlibExt.zeroEval.toAlgebra
  have hSingle : IsZero ((ChainComplex.single₀ (ModuleCat R)).obj Z) :=
    (ChainComplex.single₀ (ModuleCat R)).map_isZero hZeroObj
  have hRes : IsZero resolution.complex := by
    simp only [resolution, ProjectiveResolution.self_complex]
    exact hSingle
  have hMap : IsZero
      ((Functor.mapHomologicalComplex
        (ModuleCat.extendScalars MetaMathlibExt.zeroEval)
        (ComplexShape.down ℕ)).obj resolution.complex) :=
    Functor.map_isZero _ hRes
  have hEval : IsZero
      (((Functor.mapHomologicalComplex
        (ModuleCat.extendScalars MetaMathlibExt.zeroEval)
        (ComplexShape.down ℕ)).obj resolution.complex).X i) :=
    Functor.map_isZero
      (HomologicalComplex.eval (ModuleCat K) (ComplexShape.down ℕ) i) hMap
  exact hEval

private theorem baseSubsingleton (i : ℕ) :
    Subsingleton ↥((MetaMathlibExt.baseChangedComplex resolution).X i) :=
  ModuleCat.isZero_iff_subsingleton.mp (baseZero i)

private theorem pieceIsBot (i : ℕ) (α : Fin n →₀ Int) :
    MetaMathlibExt.baseChangedDegreePiece targetGraded resolution ι resFree i α
      = ⊥ := by
  have _hs := baseSubsingleton i
  apply le_antisymm
  · intro y _
    have hy0 : y = 0 := Subsingleton.elim _ _
    rw [hy0]
    exact Submodule.zero_mem _
  · exact bot_le

private abbrev decompAux (i : ℕ) : DirectSum.Decomposition
    (fun β => MetaMathlibExt.baseChangedDegreePiece targetGraded resolution ι resFree i β) := by
  have _hs := baseSubsingleton i
  refine { decompose' := fun _ => 0, left_inv := ?_, right_inv := ?_ } <;>
    intro x <;> exact Subsingleton.elim _ _

private theorem diffPresAux : ∀ (i : ℕ) (β : Fin n →₀ Int)
    (x : ↥((MetaMathlibExt.baseChangedComplex resolution).X (i + 1))),
    x ∈ MetaMathlibExt.baseChangedDegreePiece targetGraded resolution ι resFree (i + 1) β →
    ModuleCat.Hom.hom ((MetaMathlibExt.baseChangedComplex resolution).d (i + 1) i) x ∈
      MetaMathlibExt.baseChangedDegreePiece targetGraded resolution ι resFree i β := by
  intro i β x _
  rw [pieceIsBot i β]
  have _hs := baseSubsingleton i
  change _ = 0
  exact Subsingleton.elim _ _

private def compFn : (Fin n →₀ Int) →
    HomologicalComplex (ModuleCat K) (ComplexShape.down ℕ) :=
  fun _ => (HomologicalComplex.zero :
    HomologicalComplex (ModuleCat K) (ComplexShape.down ℕ))

private theorem compTermIsZero (i : ℕ) :
    IsZero ((HomologicalComplex.zero :
      HomologicalComplex (ModuleCat K) (ComplexShape.down ℕ)).X i) :=
  isZero_zero _

private theorem compTermSubsingleton (α : Fin n →₀ Int) (i : ℕ) :
    Subsingleton ↥((compFn α).X i) :=
  ModuleCat.isZero_iff_subsingleton.mp (compTermIsZero i)

private def inclFn (α : Fin n →₀ Int) :
    HomologicalComplex.Hom (compFn α)
      (MetaMathlibExt.baseChangedComplex resolution) where
  f := fun _ => 0
  comm' := by simp

private theorem inclInjAux : ∀ (α : Fin n →₀ Int) (i : ℕ),
    Function.Injective ⇑(ModuleCat.Hom.hom ((inclFn α).f i)) := by
  intro α i x y _
  have _hs := compTermSubsingleton α i
  have hx0 : x = 0 := Subsingleton.elim _ _
  have hy0 : y = 0 := Subsingleton.elim _ _
  rw [hx0, hy0]

private theorem rangeEqAux : ∀ (α : Fin n →₀ Int) (i : ℕ),
    LinearMap.range (ModuleCat.Hom.hom ((inclFn α).f i)) =
      MetaMathlibExt.baseChangedDegreePiece targetGraded resolution ι resFree i α := by
  intro α i
  have _hDom := compTermSubsingleton α i
  have _hCod := baseSubsingleton i
  rw [pieceIsBot i α]
  apply le_antisymm
  · rintro y ⟨w, rfl⟩
    have hw0 : w = 0 := Subsingleton.elim _ _
    have hmap0 : ModuleCat.Hom.hom ((inclFn α).f i) 0 = 0 :=
      Subsingleton.elim _ _
    rw [hw0, hmap0]
    exact Submodule.zero_mem _
  · exact bot_le

private def bc : MetaMathlibExt.MultigradedBaseChange
    targetGraded resolution ι resFree where
  decomposition := fun i => decompAux i
  diffPreserves := fun i β x hx => diffPresAux i β x hx
  comp := fun _ => (HomologicalComplex.zero :
    HomologicalComplex (ModuleCat K) (ComplexShape.down ℕ))
  incl := fun α => inclFn α
  incl_injective := fun α i => inclInjAux α i
  range_eq := fun α i => rangeEqAux α i
  hasHom := by
    intro alpha i
    exact ShortComplex.hasHomology_of_zeros _ _ _
  finiteDim := by
    intro alpha i _
    have hH : IsZero (HomologicalComplex.homology
        (HomologicalComplex.zero : HomologicalComplex (ModuleCat K)
          (ComplexShape.down ℕ)) i) :=
      ((HomologicalComplex.zero : HomologicalComplex (ModuleCat K)
        (ComplexShape.down ℕ)).sc i).isZero_homology_of_isZero_X₂
        (compTermIsZero i)
    have hSub : Subsingleton ↥(HomologicalComplex.homology
        (HomologicalComplex.zero : HomologicalComplex (ModuleCat K)
          (ComplexShape.down ℕ)) i) :=
      ModuleCat.isZero_iff_subsingleton.mp hH
    have _hFin := hSub
    exact Module.Finite.of_basis (Module.Basis.empty (ι := Empty) _)

private theorem componentHomologyIsZero (alpha : Fin n →₀ Int) (i : ℕ)
    [HomologicalComplex.HasHomology (bc.comp alpha) i] :
    IsZero (HomologicalComplex.homology (bc.comp alpha) i) := by
  apply ((bc.comp alpha).sc i).isZero_homology_of_isZero_X₂
  change IsZero ((HomologicalComplex.zero :
    HomologicalComplex (ModuleCat K) (ComplexShape.down ℕ)).X i)
  exact compTermIsZero i

private theorem betti_at_zero_is_zero :
    MetaMathlibExt.multigradedBettiNumber bc 0 0 = 0 := by
  have _hHom := bc.hasHom 0 0
  have _hFinite := bc.finiteDim 0 0
  change Module.finrank K ↥(HomologicalComplex.homology (bc.comp 0) 0) = 0
  have _hs : Subsingleton ↥(HomologicalComplex.homology (bc.comp 0) 0) :=
    ModuleCat.isZero_iff_subsingleton.mp (componentHomologyIsZero 0 0)
  exact Module.finrank_zero_of_subsingleton

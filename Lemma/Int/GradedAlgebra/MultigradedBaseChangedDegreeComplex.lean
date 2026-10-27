import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.RingTheory.GradedAlgebra.MultigradedBaseChangedDegreeComplex
open MetaMathlibExt


namespace MetaMathlibExt

/--
[mbc_finite_homology](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/GradedAlgebra/MultigradedBaseChangedDegreeComplex.lean)
-/
@[path]
whenever the ambient term is: cycles embed into the term (Noetherian) and
homology is a quotient of cycles. -/
private lemma mbc_finite_homology (K : Type u) [Field K]
  (C : HomologicalComplex (ModuleCat.{u, u} K) (ComplexShape.down Nat))
  (i : Nat) [HomologicalComplex.HasHomology C i]
  (hfin : Module.Finite K ↥(C.X i)) :
  Module.Finite K ↥(HomologicalComplex.homology C i) := by
  have := hfin
  have : IsNoetherian K ↥(C.X i) :=
    isNoetherian_of_isNoetherianRing_of_finite K ↥(C.X i)
  have hinj : Function.Injective ((C.iCycles i).hom) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have hfin_cyc : Module.Finite K ↥(C.cycles i) :=
    Module.Finite.of_injective (C.iCycles i).hom hinj
  have := hfin_cyc
  have hsurj : Function.Surjective ((C.homologyπ i).hom) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  exact Module.Finite.of_surjective (C.homologyπ i).hom hsurj

end MetaMathlibExt

namespace MetaMathlibExt

/--
[MultigradedFreeResolution.multigradedBaseChange_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/GradedAlgebra/MultigradedBaseChangedDegreeComplex.lean)
-/
@[path]
lemma MultigradedFreeResolution.multigradedBaseChange_nonempty
  {K : Type u} [Field K]
  {n : ℕ}
  {M : Type u} [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M] [Module K M]
  {targetGraded : MultigradedPolynomialModule K n M}
  {resolution : CategoryTheory.ProjectiveResolution (ModuleCat.of (MvPolynomial (Fin n) K) M)}
  {ι : ℕ → Type u}
  {res : MultigradedFreeResolution K n M targetGraded resolution ι}
-- given
  (finiteBasis : ∀ i, Finite (ι i)) :
-- imply
  Nonempty (MultigradedBaseChange targetGraded resolution ι res) := by
-- proof
  refine ⟨{
    decomposition :=
      MultigradedFreeResolution.baseChangedDegreeDecomposition targetGraded
        resolution ι res,
    diffPreserves :=
      MultigradedFreeResolution.baseChangedDifferential_preservesDegree
        targetGraded resolution ι res,
    comp := MultigradedFreeResolution.baseChangedDegreeComplex K n M
      targetGraded resolution ι res,
    incl := MultigradedFreeResolution.baseChangedDegreeInclusion K n M
      targetGraded resolution ι res,
    incl_injective :=
      MultigradedFreeResolution.baseChangedDegreeInclusion_injective K n M
        targetGraded resolution ι res,
    range_eq := MultigradedFreeResolution.baseChangedDegreeInclusion_range K n M
      targetGraded resolution ι res,
    hasHom := fun α i => inferInstance,
    finiteDim := by
      intro α i _
      have := finiteBasis i
      exact mbc_finite_homology K _ i
        (MultigradedFreeResolution.baseChangedDegreePiece_finite K n M
          targetGraded resolution ι res α i) }⟩

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26

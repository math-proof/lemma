import Mathlib
import sympy.Basic
import Instance.v1.Atlas.AlgebraicGeometryI.code.Lec2OpenSubvariety
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry CategoryTheory TopologicalSpace


namespace AlgebraicGeometry.Scheme

/--
[isAlgebraicVariety_openSubscheme](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec2OpenSubvariety.lean)
-/
@[path]
lemma isAlgebraicVariety_openSubscheme
  {k : Type u}
  [Field k]
  {X : Scheme.{u}}
  [X.Over (Spec (.of k))]
  [hX : IsAlgebraicVariety k X]
  {U : X.Opens} :
-- imply
  IsAlgebraicVariety k (↑U : Scheme.{u}) where isReduced :=
-- proof
  isReduced_of_isOpenImmersion U.ι
    locallyOfFiniteType := by
      show LocallyOfFiniteType (U.ι ≫ (X ↘ Spec (.of k)))
      exact locallyOfFiniteType_comp U.ι (X ↘ Spec (.of k))
    hasFiniteAffineCover := by
      haveI : IsLocallyNoetherian X :=
        @LocallyOfFiniteType.isLocallyNoetherian _ _ (X ↘ Spec (.of k))
          hX.locallyOfFiniteType inferInstance
      haveI : CompactSpace X := by
        obtain ⟨ι, hfin, V, haffine, hcov⟩ := hX.hasFiniteAffineCover
        rw [← isCompact_univ_iff]
        rw [← show (⋃ i, (V i : Set X)) = Set.univ from by
          rw [← Opens.coe_iSup]; simp [hcov]]
        exact isCompact_iUnion fun i => by
          haveI : IsNoetherianRing Γ(X, V i) :=
            IsLocallyNoetherian.component_noetherian ⟨V i, haffine i⟩
          haveI : NoetherianSpace (V i) := noetherianSpace_of_isAffineOpen (V i) (haffine i)
          rw [isCompact_iff_compactSpace]
          haveI : NoetherianSpace ((V i).1 : Set X) := ‹NoetherianSpace (V i)›
          infer_instance
      haveI : IsNoetherian X := ⟨⟩
      haveI : NoetherianSpace X := IsNoetherian.noetherianSpace
      haveI : NoetherianSpace (↑U : Scheme.{u}) := NoetherianSpace.set (U : Set X)
      haveI : CompactSpace (↑U : Scheme.{u}) := NoetherianSpace.compactSpace _
      let 𝒰 := (↑U : Scheme.{u}).affineCover.finiteSubcover
      refine ⟨𝒰.I₀, Fintype.ofFinite _, fun i => (𝒰.f i).opensRange,
        fun i => ?_, 𝒰.iSup_opensRange⟩
      have : IsAffine (𝒰.X i) := by
        rw [(↑U : Scheme.{u}).affineCover.finiteSubcover_X i]
        exact Scheme.isAffine_affineCover _ _
      exact isAffineOpen_opensRange (𝒰.f i)

end AlgebraicGeometry.Scheme


-- created on 2026-10-23

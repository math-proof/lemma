import Mathlib
import sympy.Basic

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

/--
[AlgebraicGeometry_Scheme_Hom_eq_of_fromSpecStalk_genericPoint_comp_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_eq_of_fromSpecStalk_genericPoint_comp_eq.lean)
-/
@[main]
private lemma main
  {U H S : Scheme.{u}} [IsIntegral U]
  {sU : U ⟶ S}
  {sH : H ⟶ S} [IsSeparated sH]
  {f g : U ⟶ H}
-- given
  (hf : f ≫ sH = sU)
  (hg : g ≫ sH = sU)
  (h : U.fromSpecStalk (genericPoint U) ≫ f = U.fromSpecStalk (genericPoint U) ≫ g) :
-- imply
  f = g := by
-- proof
  have : IsDominant (U.fromSpecStalk (genericPoint U)) := by
    constructor
    have hmem : genericPoint U ∈ Set.range (U.fromSpecStalk (genericPoint U)).base :=
      ⟨IsLocalRing.closedPoint _, Scheme.fromSpecStalk_closedPoint⟩
    have hd : Dense ({genericPoint U} : Set U) := by
      rw [dense_iff_closure_eq]
      exact genericPoint_closure U
    exact hd.mono (Set.singleton_subset_iff.mpr hmem)
  exact ext_of_isDominant_of_isSeparated sH (hf.trans hg.symm) (U.fromSpecStalk (genericPoint U)) h


-- created on 2026-10-05

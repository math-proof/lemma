/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.SetTheory.Cardinal.Free
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Pi.Irrational
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.MetricSpace.IsometricSMul
import Def.MeasureTheory.Geometry.BanachTarski


namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/-- btCongr is reflexive. -/
theorem btCongr_refl {X : Type*} [MetricSpace X] (A : Set X) :
    btCongr A A := by
  refine ⟨id, {IsometryEquiv.refl X}, Set.finite_singleton _,
    ⟨fun x hx => hx, fun x _ y _ h => h, fun y hy => ⟨y, hy, rfl⟩⟩, ?_⟩
  intro x _
  exact ⟨IsometryEquiv.refl X, rfl, rfl⟩

/-- btCongr is symmetric. -/
theorem btCongr_symm {X : Type*} [MetricSpace X] {A B : Set X}
    (h : btCongr A B) : btCongr B A := by
  obtain ⟨f, S, hfin, hbij, hloc⟩ := h
  by_cases hA : A.Nonempty
  · obtain ⟨x₀, hx₀⟩ := hA
    have : Nonempty X := ⟨x₀⟩
    have hinv : Set.InvOn f (Function.invFunOn f A) B A :=
      ⟨(hbij.invOn_invFunOn).2, (hbij.invOn_invFunOn).1⟩
    have hbij' : Set.BijOn (Function.invFunOn f A) B A :=
      Set.BijOn.symm hinv hbij
    refine ⟨Function.invFunOn f A, S.image IsometryEquiv.symm, hfin.image _,
      hbij', ?_⟩
    intro y hyB
    have hxA : Function.invFunOn f A y ∈ A := hbij'.mapsTo hyB
    have hfy : f (Function.invFunOn f A y) = y := hinv.1 hyB
    obtain ⟨g, hgS, hgx⟩ := hloc _ hxA
    refine ⟨g.symm, ⟨g, hgS, rfl⟩, ?_⟩
    rw [hfy] at hgx
    have hgg : Function.invFunOn f A y =
        g.symm (g (Function.invFunOn f A y)) := by
      rw [IsometryEquiv.symm_apply_apply]
    rw [hgg, ← hgx]
  · have hB : B = ∅ := by
      rw [← Set.not_nonempty_iff_eq_empty]
      intro hne
      obtain ⟨y, hy⟩ := hne
      obtain ⟨x, hxA, -⟩ := hbij.2.2 hy
      exact hA ⟨x, hxA⟩
    have hA' : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA
    subst hB
    subst hA'
    exact btCongr_refl ∅

/-- btCongr is transitive. -/
theorem btCongr_trans {X : Type*} [MetricSpace X] {A B C : Set X}
    (h1 : btCongr A B) (h2 : btCongr B C) : btCongr A C := by
  obtain ⟨f1, S1, hfin1, hbij1, hloc1⟩ := h1
  obtain ⟨f2, S2, hfin2, hbij2, hloc2⟩ := h2
  refine ⟨f2 ∘ f1, S1.image2 (fun g1 g2 => g1.trans g2) S2, hfin1.image2 _ hfin2,
    hbij2.comp hbij1, ?_⟩
  intro x hxA
  obtain ⟨g1, hg1, hg1x⟩ := hloc1 x hxA
  obtain ⟨g2, hg2, hg2x⟩ := hloc2 (f1 x) (hbij1.mapsTo hxA)
  refine ⟨g1.trans g2, Set.mem_image2_of_mem hg1 hg2, ?_⟩
  rw [Function.comp_apply, IsometryEquiv.trans_apply, hg1x]
  rw [hg1x] at hg2x
  exact hg2x

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

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
import Def.MeasureTheory.Geometry.BanachTarski.Part16


namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/-- The bijection form converts to the indexed-pieces form. -/
theorem btCongr_toWanted {X : Type*} [MetricSpace X] {A B : Set X}
    (h : btCongr A B) : FinitelyEquidecomposableByIsometries A B := by
  obtain ⟨f, S, hfin, hbij, hloc⟩ := h
  classical
  by_cases hS : S.Nonempty
  · have := hfin.fintype
    set n := Fintype.card ↥S with hn
    set e := Fintype.equivFin ↥S with he
    obtain ⟨g0, hg0⟩ := hS
    set i0 : Fin n := e ⟨g0, hg0⟩ with hi0
    set gs : Fin n → X ≃ᵢ X := fun i => (e.symm i).val with hgs
    have ch : ∀ x : {x // x ∈ A}, ∃ i : Fin n, f x.val = gs i x.val := by
      intro x
      obtain ⟨g, hgS, hgx⟩ := hloc x.val x.property
      refine ⟨e ⟨g, hgS⟩, ?_⟩
      change f x.val = ((e.symm (e ⟨g, hgS⟩)).val) x.val
      rw [Equiv.symm_apply_apply]
      exact hgx
    set idx : X → Fin n := fun x =>
      if h : x ∈ A then Classical.choose (ch ⟨x, h⟩) else i0 with hidx
    have hidx_eq : ∀ (x : X) (h : x ∈ A),
        idx x = Classical.choose (ch ⟨x, h⟩) := fun x h => dite_eq_left h
    set As : Fin n → Set X := fun i => {x ∈ A | idx x = i} with hAs
    set Bs : Fin n → Set X := fun i => gs i '' As i with hBs
    have hagree : ∀ (i : Fin n) (x : X), x ∈ As i → f x = gs i x := by
      intro i x hx
      obtain ⟨hxA, hxi⟩ := hx
      have h1 : f x = gs (Classical.choose (ch ⟨x, hxA⟩)) x :=
        Classical.choose_spec (ch ⟨x, hxA⟩)
      rw [← hidx_eq x hxA, hxi] at h1
      exact h1
    have hBs_eq : ∀ i, Bs i = f '' As i := by
      intro i
      change gs i '' As i = f '' As i
      exact Set.image_congr (fun x hx => (hagree i x hx).symm)
    have hAs_union : (⋃ i, As i) = A := by
      apply Set.Subset.antisymm
      · exact Set.iUnion_subset (fun i x hx => hx.1)
      · intro x hx
        exact Set.mem_iUnion.mpr ⟨idx x, hx, rfl⟩
    have hdisjA : ∀ i j, i ≠ j → Disjoint (As i) (As j) := by
      intro i j hij
      rw [Set.disjoint_left]
      rintro x ⟨-, hxi⟩ ⟨-, hxj⟩
      exact hij (hxi.symm.trans hxj)
    have hdisjB : ∀ i j, i ≠ j → Disjoint (Bs i) (Bs j) := by
      intro i j hij
      rw [hBs_eq i, hBs_eq j]
      have hsub : ∀ k, As k ⊆ A := fun k x hx => hx.1
      have hinter : f '' As i ∩ f '' As j = ∅ := by
        rw [← hbij.2.1.image_inter (hsub i) (hsub j),
          Set.disjoint_iff_inter_eq_empty.mp (hdisjA i j hij), Set.image_empty]
      exact Set.disjoint_iff_inter_eq_empty.mpr hinter
    have hB_union : (⋃ i, Bs i) = B := by
      apply Set.Subset.antisymm
      · intro y hy
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
        rw [hBs_eq i] at hi
        obtain ⟨x, hx, hfx⟩ := hi
        subst hfx
        exact hbij.mapsTo (hAs_union ▸ Set.mem_iUnion.mpr ⟨i, hx⟩)
      · intro y hyB
        rw [← hbij.image_eq] at hyB
        obtain ⟨x, hxA, hfx⟩ := hyB
        rw [← hAs_union] at hxA
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxA
        have hagi := hagree i x hi
        exact Set.mem_iUnion.mpr ⟨i, x, hi, by rw [← hagi]; exact hfx⟩
    exact ⟨n, As, Bs, gs, hdisjA, hdisjB, hAs_union, hB_union, fun i => rfl⟩
  · rw [Set.not_nonempty_iff_eq_empty] at hS
    have hA : A = ∅ := Set.eq_empty_of_forall_notMem (fun x hx => by
      obtain ⟨g, hgS, -⟩ := hloc x hx
      rw [hS] at hgS
      exact hgS)
    have hB : B = ∅ := by
      have himg := hbij.image_eq
      rw [hA, Set.image_empty] at himg
      exact himg.symm
    subst hA
    subst hB
    refine ⟨0, fun _ => ∅, fun _ => ∅, fun _ => IsometryEquiv.refl X,
      ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      exact i.elim0
    · intro i
      exact i.elim0
    · simp
    · simp
    · intro i
      exact i.elim0

/-- From indexed pieces to the bijection form. -/
theorem btCongr_ofWanted {X : Type*} [MetricSpace X] {A B : Set X}
    (h : FinitelyEquidecomposableByIsometries A B) : btCongr A B := by
  classical
  obtain ⟨n, As, Bs, gs, hdisjA, hdisjB, hUnionA, hUnionB, himg⟩ := h
  have hex : ∀ x : X, x ∈ A → ∃ i, x ∈ As i := by
    intro x hx
    rw [← hUnionA] at hx
    exact Set.mem_iUnion.mp hx
  have hspec : ∀ (x : X) (h : x ∈ A), x ∈ As (Classical.choose (hex x h)) :=
    fun x h => Classical.choose_spec (hex x h)
  have hchoice_eq : ∀ (x : X) (hxA : x ∈ A) (i : Fin n), x ∈ As i →
      Classical.choose (hex x hxA) = i := by
    intro x hxA i hi
    by_contra hne
    exact Set.disjoint_left.mp (hdisjA _ _ hne) (hspec x hxA) hi
  refine ⟨fun x => if h : x ∈ A then gs (Classical.choose (hex x h)) x else x,
    Set.range gs, Set.finite_range gs, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro x hxA
    simp only [dite_eq_left hxA]
    have hmem : gs (Classical.choose (hex x hxA)) x ∈
        gs (Classical.choose (hex x hxA)) '' As (Classical.choose (hex x hxA)) :=
      ⟨x, hspec x hxA, rfl⟩
    rw [himg] at hmem
    rw [← hUnionB]
    exact Set.mem_iUnion.mpr ⟨_, hmem⟩
  · intro x hxA y hyA hxy
    simp only [dite_eq_left hxA, dite_eq_left hyA] at hxy
    have hxBs : gs (Classical.choose (hex x hxA)) x ∈
        Bs (Classical.choose (hex x hxA)) := by
      have hmem : gs (Classical.choose (hex x hxA)) x ∈
          gs (Classical.choose (hex x hxA)) '' As (Classical.choose (hex x hxA)) :=
        ⟨x, hspec x hxA, rfl⟩
      rwa [himg] at hmem
    have hyBs : gs (Classical.choose (hex y hyA)) y ∈
        Bs (Classical.choose (hex y hyA)) := by
      have hmem : gs (Classical.choose (hex y hyA)) y ∈
          gs (Classical.choose (hex y hyA)) '' As (Classical.choose (hex y hyA)) :=
        ⟨y, hspec y hyA, rfl⟩
      rwa [himg] at hmem
    have hij : Classical.choose (hex x hxA) = Classical.choose (hex y hyA) := by
      by_contra hne
      have hxBs' : gs (Classical.choose (hex y hyA)) y ∈
          Bs (Classical.choose (hex x hxA)) := hxy ▸ hxBs
      exact Set.disjoint_left.mp (hdisjB _ _ hne) hxBs' hyBs
    rw [hij] at hxy
    exact (gs _).injective hxy
  · intro y hyB
    rw [← hUnionB] at hyB
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hyB
    rw [← himg i] at hi
    obtain ⟨x, hxAs, hgx⟩ := hi
    have hxmem : x ∈ ⋃ i, As i := Set.mem_iUnion.mpr ⟨i, hxAs⟩
    have hxA : x ∈ A := hUnionA ▸ hxmem
    have hci : Classical.choose (hex x hxA) = i := hchoice_eq x hxA i hxAs
    refine ⟨x, hxA, ?_⟩
    simp only [dite_eq_left hxA]
    rw [hci]
    exact hgx
  · intro x hxA
    exact ⟨gs (Classical.choose (hex x hxA)), Set.mem_range_self _,
      by simp only [dite_eq_left hxA]⟩

/-- Finite equidecomposability holds iff there is a piecewise-isometric bijection. -/
theorem finitelyEquidecomposableByIsometries_iff_bijOn
    {X : Type*} [MetricSpace X] (A B : Set X) :
    FinitelyEquidecomposableByIsometries A B ↔
      ∃ (f : X → X) (S : Set (X ≃ᵢ X)),
        S.Finite ∧ Set.BijOn f A B ∧ ∀ x ∈ A, ∃ g ∈ S, f x = g x := by
  constructor
  · intro h
    exact btCongr_ofWanted h
  · intro h
    exact btCongr_toWanted h

namespace FinitelyEquidecomposableByIsometries

/-- Finite equidecomposability is reflexive. -/
theorem refl {X : Type*} [MetricSpace X] (A : Set X) :
    FinitelyEquidecomposableByIsometries A A :=
  btCongr_toWanted (btCongr_refl A)

/-- Finite equidecomposability is symmetric. -/
theorem symm {X : Type*} [MetricSpace X] {A B : Set X}
    (h : FinitelyEquidecomposableByIsometries A B) :
    FinitelyEquidecomposableByIsometries B A :=
  btCongr_toWanted (btCongr_symm (btCongr_ofWanted h))

/-- Finite equidecomposability is transitive. -/
theorem trans {X : Type*} [MetricSpace X] {A B C : Set X}
    (h1 : FinitelyEquidecomposableByIsometries A B)
    (h2 : FinitelyEquidecomposableByIsometries B C) :
    FinitelyEquidecomposableByIsometries A C :=
  btCongr_toWanted (btCongr_trans (btCongr_ofWanted h1) (btCongr_ofWanted h2))

/-- Finite equidecomposability is closed under disjoint unions. -/
theorem union {X : Type*} [MetricSpace X] {A₁ A₂ B₁ B₂ : Set X}
    (h1 : FinitelyEquidecomposableByIsometries A₁ B₁)
    (h2 : FinitelyEquidecomposableByIsometries A₂ B₂)
    (hdA : Disjoint A₁ A₂) (hdB : Disjoint B₁ B₂) :
    FinitelyEquidecomposableByIsometries (A₁ ∪ A₂) (B₁ ∪ B₂) :=
  btCongr_toWanted (btCongr_union (btCongr_ofWanted h1) (btCongr_ofWanted h2) hdA hdB)

/-- An isometry maps a set to its image equidecomposably. -/
theorem image_isometryEquiv {X : Type*} [MetricSpace X]
    (g : X ≃ᵢ X) (A : Set X) :
    FinitelyEquidecomposableByIsometries A (g '' A) :=
  btCongr_toWanted (btCongr_self_image g A)

end FinitelyEquidecomposableByIsometries

/--
The closed unit ball at `0` in `EuclideanSpace ℝ (Fin 3)` is finitely equidecomposable by ambient
bijective isometries with the disjoint union of two closed unit balls `closedBall c₁ 1 ∪
closedBall c₂ 1` for some centres `c₁ c₂` with `Disjoint`. Source: S. Banach and A. Tarski, Fund.
Math. 6 (1924) 244–277 original paradox; S. Wagon, The Banach–Tarski Paradox, Cambridge Univ.
Press (1993); Lean states closed unit ball duplication specialization in ℝ³ with ambient `≃ᵢ`
equidecomposability.

Proves `Wanted` entry `banach_tarski_closedBall_unit`.
-/
theorem banach_tarski_closedBall_unit :
    ∃ (c₁ c₂ : EuclideanSpace ℝ (Fin 3)),
      Disjoint (Metric.closedBall c₁ 1) (Metric.closedBall c₂ 1) ∧
      FinitelyEquidecomposableByIsometries
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
        (Metric.closedBall c₁ 1 ∪ Metric.closedBall c₂ 1) := by
  obtain ⟨hcongr, himg, hdisj⟩ := btCongr_ball_double
  refine ⟨0, btC₂, ?_, ?_⟩
  · rw [← himg]
    exact hdisj
  · have h := btCongr_toWanted hcongr
    rw [himg] at h
    exact h

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

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
import Def.MeasureTheory.Geometry.BanachTarski.Part11


namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/-- The chosen element moves the representative to `x`. -/
theorem btGamma_spec (x : {x : btE // x ∈ btOmega}) :
    btAct (btGamma x) (btRep x).val = x.val :=
  Classical.choose_spec (btRep_mem x)

/-- The free locus acts freely. -/
theorem btOmega_free (x : btE) (hx : x ∈ btOmega)
    (w v : FreeGroup (Fin 2)) (h : btAct w x = btAct v x) : w = v := by
  have hfix : btAct (v⁻¹ * w) x = x := by
    have e1 : btAct (v⁻¹ * w) x = btAct v⁻¹ (btAct w x) := btAct_mul _ _ _
    rw [e1, h]
    exact btAct_inv v x
  by_cases huv : v⁻¹ * w = 1
  · have e : v * (v⁻¹ * w) = v * 1 := congrArg (v * ·) huv
    rw [mul_inv_cancel_left, mul_one] at e
    exact e
  · exfalso
    simp only [btOmega] at hx
    obtain ⟨-, hnb⟩ := hx
    have hx0 : x ≠ 0 := fun hz => hnb (Or.inl hz)
    exact hnb (Or.inr ⟨hx0, v⁻¹ * w, huv, hfix⟩)

/-- The free locus is invariant. -/
theorem btOmega_invariant (w : FreeGroup (Fin 2))
    (x : btE) (hx : x ∈ btOmega) : btAct w x ∈ btOmega := by
  simp only [btOmega] at hx ⊢
  obtain ⟨hxB, hxn⟩ := hx
  refine ⟨?_, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right]
    change ‖btIsoOfUnitary (btRho w) x‖ ≤ 1
    rw [btIsoOfUnitary_norm]
    rw [Metric.mem_closedBall, dist_zero_right] at hxB
    exact hxB
  · simp only [Set.mem_union, Set.mem_singleton_iff] at hxn ⊢
    intro hcon
    rcases hcon with h0 | hbad
    · have hx0 : x = 0 := by
        have e := btAct_inv w x
        rw [h0] at e
        have e0 : btAct w⁻¹ (0 : btE) = 0 := btIsoOfUnitary_zero _
        rw [e0] at e
        exact e.symm
      exact (fun hz => hxn (Or.inl hz)) hx0
    · simp only [btBad, Set.mem_ofPred_eq] at hbad
      obtain ⟨-, h, hh, hfix⟩ := hbad
      have hconj : btAct (w⁻¹ * h * w) x = x := by
        rw [btAct_mul, btAct_mul, hfix]
        exact btAct_inv w x
      have hne1 : w⁻¹ * h * w ≠ 1 := by
        intro hcon1
        have e : w * (w⁻¹ * h * w) * w⁻¹ = h := by group
        rw [hcon1] at e
        simp at e
        exact hh e.symm
      have hx0 : x ≠ 0 := fun hz => hxn (Or.inl hz)
      exact hxn (Or.inr ⟨hx0, w⁻¹ * h * w, hne1, hconj⟩)

/-- The cocycle identity. -/
theorem btGamma_act (h : FreeGroup (Fin 2)) (x : {x : btE // x ∈ btOmega})
    (hx : btAct h x.val ∈ btOmega) :
    btGamma ⟨btAct h x.val, hx⟩ = h * btGamma x := by
  have hrep : btRep ⟨btAct h x.val, hx⟩ = btRep x :=
    (btRep_orbit x ⟨btAct h x.val, hx⟩ ⟨h, rfl⟩).symm
  have h1 := btGamma_spec ⟨btAct h x.val, hx⟩
  have h2 := btGamma_spec x
  have h3 : btAct (h * btGamma x) (btRep ⟨btAct h x.val, hx⟩).val =
      btAct h x.val := by
    rw [btAct_mul, hrep, h2]
  have hfree := btOmega_free (btRep ⟨btAct h x.val, hx⟩).val
    (btRep ⟨btAct h x.val, hx⟩).property _ _ (h1.trans h3.symm)
  exact hfree

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

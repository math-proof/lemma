import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.BlowupChart
open Polynomial


/--
[blowupChartMap_eq_comp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BlowupChart.lean)
-/
@[path]
lemma blowupChartMap_eq_comp
  {k : Type*}
  [CommRing k]
  {p : Polynomial (Polynomial k)} :
-- imply
  blowupChartMap k p = p.comp (C X * X) := by
-- proof
  simp [blowupChartMap, comp]

/--
[blowupChartMap_X](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BlowupChart.lean)
-/
@[path]
lemma blowupChartMap_X
  {k : Type*}
  [CommRing k] :
-- imply
  blowupChartMap k X = C (X : Polynomial k) * X := by
-- proof
  simp [blowupChartMap]

/--
[blowupChartMap_C](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BlowupChart.lean)
-/
@[path]
lemma blowupChartMap_C
  {k : Type*}
  [CommRing k]
  {a : Polynomial k} :
-- imply
  blowupChartMap k (C a) = C a := by
-- proof
  simp [blowupChartMap]

/--
[blowupChartMap_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BlowupChart.lean)
-/
@[path]
lemma blowupChartMap_injective
  {k : Type*}
  [CommRing k]
  [IsDomain k] :
-- imply
  Function.Injective (blowupChartMap k) := by
-- proof
  intro p q hpq
  rw [← sub_eq_zero]
  have h : blowupChartMap k (p - q) = 0 := by rw [map_sub, sub_eq_zero, hpq]
  rw [blowupChartMap_eq_comp] at h
  rw [comp_eq_zero_iff] at h
  obtain h1 | ⟨_, hq⟩ := h
  · exact h1
  · exfalso
    have h0 : (C (X : Polynomial k) * X : Polynomial (Polynomial k)).coeff 0 = 0 := by
      simp [coeff_mul]
    rw [h0, map_zero] at hq
    have : (C (X : Polynomial k) * X : Polynomial (Polynomial k)) ≠ 0 := by
      intro h0
      have := congr_arg (fun p => coeff p 1) h0
      simp at this
    exact this hq


-- created on 2026-10-23

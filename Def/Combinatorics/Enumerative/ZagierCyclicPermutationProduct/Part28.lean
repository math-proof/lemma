/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.GroupTheory.Perm.Fin
import Def.Combinatorics.Enumerative.Stirling.Part4
import Lemma.Finset.Enumerative.Stirling
import Structure.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part6
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

noncomputable def zagFullSlice {n : ℕ} (p : ZagPointedPlane n) :
    ZagFullSliceResult p := by
  classical
  let e' := zagSliceOrder p.order p.vertical p.point p.point_property
  let π' := zagSliceVertical p.order p.vertical p.point p.point_property
  if hres : zagNontrivialAntiExceedance e' π' p.point then
    let m := zagSliceResidualTriple p.order p.vertical p.point
      p.point_property hres
    let p' : ZagPointedPlane n := ⟨e', π', p.point, hres⟩
    let next := zagFullSlice p'
    have hmfirst : m.first ∈ zagCycleMinima next.out.order next.out.vertical := by
      apply next.preserves_before m.first
      · exact m.first_lt_middle.trans m.middle_lt_third
      · exact m.first_mem
    have hmmiddle : m.middle ∈ zagCycleMinima next.out.order next.out.vertical := by
      apply next.preserves_before m.middle m.middle_lt_third m.middle_mem
    have hmiddle_root : m.middle < next.out.root := by
      rw [next.root_eq]
      exact m.middle_lt_third
    exact {
      out := {
        order := next.out.order
        vertical := next.out.vertical
        root := m.first
        marks := .prepend m.first m.middle next.out.root hmfirst hmmiddle
          m.first_lt_middle hmiddle_root next.out.marks
      }
      root_eq := rfl
      preserves_before := by
        intro r hr hmem
        apply next.preserves_before r
        · exact hr.trans (m.first_lt_middle.trans m.middle_lt_third)
        · exact zagSlice_cycleMinPos_before p.order p.vertical p.point r
            p.point_property hmem hr
    }
  else
    let m := zagSliceTerminalTriple p.order p.vertical p.point
      p.point_property hres
    exact {
      out := ⟨e', π', m.first, .terminal m⟩
      root_eq := rfl
      preserves_before := fun r hr hmem =>
        zagSlice_cycleMinPos_before p.order p.vertical p.point r
          p.point_property hmem hr
    }
termination_by n - (zagCycleMinPos p.order p.vertical p.point).val
decreasing_by
  have hlt : zagCycleMinPos p.order p.vertical p.point <
      zagCycleMinPos e' π' p.point := by
    exact m.first_lt_middle.trans m.middle_lt_third
  change n - (zagCycleMinPos e' π' p.point).val <
    n - (zagCycleMinPos p.order p.vertical p.point).val
  omega

end MetaMathlibExt

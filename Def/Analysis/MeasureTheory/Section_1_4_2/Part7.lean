import Mathlib.SetTheory.Cardinal.Aleph
import Instance.Analysis.MeasureTheory.Section_1_4_1.Part4
import Theorem.Analysis.MeasureTheory.Section_1_4_2.Part5


def ConcreteSigmaAlgebra.measurableSpace {X: Type*} (B: ConcreteSigmaAlgebra X) : MeasurableSpace X := {
  MeasurableSet' := B.measurable
  measurableSet_empty := B.empty_mem
  measurableSet_compl := B.compl_mem
  measurableSet_iUnion := B.countable_union_mem
}

def MeasurableSpace.sigmaAlgebra {X: Type*} (M: MeasurableSpace X) : ConcreteSigmaAlgebra X := {
  measurable := M.MeasurableSet'
  empty_mem := M.measurableSet_empty
  compl_mem := M.measurableSet_compl
  union_mem := fun E F hE hF => by
    have hunion : E ∪ F = ⋃ n, if n = 0 then E else F := by
      ext x
      simp only [Set.mem_union, Set.mem_iUnion]
      constructor
      · rintro (hx | hx)
        · exact ⟨0, by simp [hx]⟩
        · exact ⟨1, by simp [hx]⟩
      · rintro ⟨n, hx⟩
        by_cases hn : n = 0
        · exact Or.inl (by simpa [hn] using hx)
        · exact Or.inr (by simpa [hn] using hx)
    rw [hunion]
    exact M.measurableSet_iUnion _ (fun n => by
      by_cases hn : n = 0
      · simpa [hn] using hE
      · simpa [hn] using hF)
  countable_union_mem := M.measurableSet_iUnion
}


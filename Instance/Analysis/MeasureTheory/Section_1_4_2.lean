import Mathlib.SetTheory.Cardinal.Aleph
import Instance.Analysis.MeasureTheory.Section_1_4_1.Part4
import Def.Analysis.MeasureTheory.Section_1_4_2.Part4


instance ConcreteSigmaAlgebra.instLE (X:Type*) : LE (ConcreteSigmaAlgebra X) :=
  ⟨fun B1 B2 => ∀ E, B1.measurable E → B2.measurable E⟩

instance ConcreteSigmaAlgebra.instPartialOrder (X:Type*) : PartialOrder (ConcreteSigmaAlgebra X) :=
  {
    le_refl := fun B E hE => hE
    le_trans := fun A B C hAB hBC E hE => hBC E (hAB E hE)
    le_antisymm := by
      intro A B hAB hBA
      have h : A.toConcreteBooleanAlgebra = B.toConcreteBooleanAlgebra :=
        le_antisymm hAB hBA
      cases A
      cases B
      cases h
      rfl
  }

instance ConcreteSigmaAlgebra.instOrderTop {X:Type*} : OrderTop (ConcreteSigmaAlgebra X) :=
  {
    top := {
      measurable := fun _ => True
      empty_mem := trivial
      compl_mem := fun _ _ => trivial
      union_mem := fun _ _ _ _ => trivial
      countable_union_mem := fun _ _ => trivial
    }
    le_top := fun _ _ _ => trivial
  }

instance ConcreteSigmaAlgebra.instOrderBot {X:Type*} : OrderBot (ConcreteSigmaAlgebra X) :=
  {
    bot := {
      measurable := fun E => E = ∅ ∨ E = Set.univ
      empty_mem := by grind
      compl_mem := fun E hE => by grind
      union_mem := fun E F hE hF => by grind
      countable_union_mem := fun E hE => by
        by_cases h : ∃ n, E n = Set.univ
        · obtain ⟨n, hn⟩ := h
          refine Or.inr ?_
          ext x
          simp
          exact ⟨n, by simp [hn]⟩
        · refine Or.inl ?_
          ext x
          simp
          intro n
          have hEn := hE n
          rcases hEn with h0 | h1
          · simp [h0]
          · exact (h ⟨n, h1⟩).elim
    }
    bot_le := fun B E hE => by
      rcases hE with h | h
      · simpa [h] using B.empty_mem
      · simpa [h, Set.compl_empty] using B.compl_mem ∅ B.empty_mem
  }

/-- Exercise 1.4.13 (Intersection of sigma-algebras) -/
instance ConcreteSigmaAlgebra.instInfSet {X:Type*} : InfSet (ConcreteSigmaAlgebra X) :=
  {
      sInf S :=
        {
          measurable := fun E => ∀ B ∈ S, B.measurable E
          empty_mem := fun B _ => B.empty_mem
          compl_mem := fun E hE B hB => B.compl_mem E (hE B hB)
          union_mem := fun E F hE hF B hB => B.union_mem E F (hE B hB) (hF B hB)
          countable_union_mem := fun E hE B hB => B.countable_union_mem E (fun n => hE n B hB)
        }
  }


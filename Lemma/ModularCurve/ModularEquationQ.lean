import Mathlib
import Lemma.ModularCurve.JqCoeff
import Lemma.ModularCurve.X0

set_option autoImplicit false

noncomputable section

namespace ModularCurve

section JLine

variable (K : Type*) [Field K] (M : ℕ) [NeZero M]

def jqNField : IntermediateField K (LaurentSeries K) :=
  IntermediateField.adjoin K {jqNModC K M}

theorem jqNModC_mem_jqNField : jqNModC K M ∈ jqNField K M :=
  IntermediateField.subset_adjoin K _ (Set.mem_singleton _)

def jqNGen : jqNField K M :=
  ⟨jqNModC K M, jqNModC_mem_jqNField K M⟩

@[simp]
theorem coe_jqNGen : (jqNGen K M : LaurentSeries K) = jqNModC K M := rfl

end JLine

namespace ModularPolynomialData

variable {M : ℕ} [NeZero M] (data : ModularPolynomialData M) (K : Type*) [Field K]

def toJqNField : Polynomial (jqNField K M) :=
  data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (jqNField K M)) (jqNGen K M))

theorem toJqNField_monic : (data.toJqNField K).Monic :=
  data.monic.map _

theorem toJqNField_map :
    (data.toJqNField K).map (algebraMap (jqNField K M) (LaurentSeries K)) =
      data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
        (qExpand K M (jqModC K))) := by
  rw [toJqNField, Polynomial.map_map]
  congr 1
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  rw [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_X, Polynomial.eval₂_X]
  rfl

def rootField : IntermediateField K (LaurentSeries K) :=
  IntermediateField.adjoin K (insert (jqNModC K M) ((data.toJqNField K).rootSet (LaurentSeries K)))

theorem jqNField_le_rootField : jqNField K M ≤ data.rootField K :=
  IntermediateField.adjoin.mono K _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))

theorem rootSet_subset_rootField :
    (data.toJqNField K).rootSet (LaurentSeries K) ⊆ (data.rootField K : Set (LaurentSeries K)) :=
  (Set.subset_insert _ _).trans (IntermediateField.subset_adjoin K _)

end ModularPolynomialData

end ModularCurve

end

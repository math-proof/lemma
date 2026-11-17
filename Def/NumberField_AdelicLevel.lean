module

public import Structure.NumberField_AdelicLevel

@[expose] public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField RestrictedProduct Matrix
open scoped Topology

noncomputable section

namespace NumberField.AdelicLevel

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

section Projections

def archEval (w : InfinitePlace K) : InfiniteAdeleRing K →+* w.Completion where
  toFun a := a w
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def adeleArch : AdeleRing R K →+* InfiniteAdeleRing K where
  toFun a := a.1
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def archComponent (w : InfinitePlace K) : GL (Fin 2) (InfiniteAdeleRing K) →* GL (Fin 2) w.Completion :=
  Matrix.GeneralLinearGroup.map (archEval K w)

def glArch : GL (Fin 2) (AdeleRing R K) →* GL (Fin 2) (InfiniteAdeleRing K) :=
  Matrix.GeneralLinearGroup.map (adeleArch R K)

end Projections

section Gen

def finIncl : FiniteAdeleRing R K →* AdeleRing R K where
  toFun x := ((1 : InfiniteAdeleRing K), x)
  map_one' := rfl
  map_mul' _ _ := Prod.ext (one_mul _).symm rfl

variable (v : HeightOneSpectrum R)

open scoped Classical in

def localUnit : (v.adicCompletion K)ˣ →* (FiniteAdeleRing R K)ˣ where
  toFun t :=
    { val := ⟨Function.update 1 v (t : v.adicCompletion K),
        Filter.eventually_cofinite.mpr ((Set.finite_singleton v).subset fun w hw => by
          by_contra hwv
          exact hw (by rw [Function.update_of_ne hwv]; exact one_mem _))⟩
      inv := ⟨Function.update 1 v ((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K),
        Filter.eventually_cofinite.mpr ((Set.finite_singleton v).subset fun w hw => by
          by_contra hwv
          exact hw (by rw [Function.update_of_ne hwv]; exact one_mem _))⟩
      val_inv := by
        refine Subtype.ext (funext fun w => ?_)
        show Function.update (1 : ∀ w : HeightOneSpectrum R, w.adicCompletion K) v
            (t : v.adicCompletion K) w *
          Function.update (1 : ∀ w : HeightOneSpectrum R, w.adicCompletion K) v
            ((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) w = 1
        by_cases hw : w = v
        · subst hw; simp
        · simp [Function.update_of_ne hw]
      inv_val := by
        refine Subtype.ext (funext fun w => ?_)
        show Function.update (1 : ∀ w : HeightOneSpectrum R, w.adicCompletion K) v
            ((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) w *
          Function.update (1 : ∀ w : HeightOneSpectrum R, w.adicCompletion K) v
            (t : v.adicCompletion K) w = 1
        by_cases hw : w = v
        · subst hw; simp
        · simp [Function.update_of_ne hw] }
  map_one' := by
    refine Units.ext (Subtype.ext (funext fun w => ?_))
    show Function.update (1 : ∀ w : HeightOneSpectrum R, w.adicCompletion K) v 1 w = 1
    by_cases hw : w = v
    · subst hw; simp
    · simp [Function.update_of_ne hw]
  map_mul' t t' := by
    refine Units.ext (Subtype.ext (funext fun w => ?_))
    show Function.update (1 : ∀ w : HeightOneSpectrum R, w.adicCompletion K) v
        ((t * t' : (v.adicCompletion K)ˣ) : v.adicCompletion K) w =
      Function.update (1 : ∀ w : HeightOneSpectrum R, w.adicCompletion K) v
          (t : v.adicCompletion K) w *
        Function.update (1 : ∀ w : HeightOneSpectrum R, w.adicCompletion K) v
          (t' : v.adicCompletion K) w
    by_cases hw : w = v
    · subst hw; simp
    · simp [Function.update_of_ne hw]

variable {R K v}

variable (K v)

def uniformizer : R := Classical.choose v.intValuation_exists_uniformizer

def uniformizerUnit : (v.adicCompletion K)ˣ :=
  Units.mk0 (algebraMap K (v.adicCompletion K) (algebraMap R K (uniformizer v))) fun h => by
    have hval :
        Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K (uniformizer v)))
          = WithZero.exp (-1 : ℤ) := by
      rw [show algebraMap K (v.adicCompletion K) (algebraMap R K (uniformizer v)) =
          ((algebraMap R K (uniformizer v) : K) : v.adicCompletion K) from rfl,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
        HeightOneSpectrum.valuation_of_algebraMap]
      exact Classical.choose_spec v.intValuation_exists_uniformizer
    rw [h, map_zero] at hval
    exact WithZero.exp_ne_zero hval.symm

end Gen

end NumberField.AdelicLevel

end

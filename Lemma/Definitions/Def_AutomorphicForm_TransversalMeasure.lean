import Lemma.Definitions.Def_AutomorphicForm_TwistedOrbital
import Lemma.Definitions.Def_NumberField_IdeleBox
import Lemma.Definitions.Def_M4aHerbrand_GenuineBeta

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct Pointwise

namespace AutomorphicForm.TransversalMeasure

section Definitions

noncomputable def integralUnits (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) : Subgroup (L ⊗[K] v.adicCompletion K)ˣ :=
  (HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v).range.toSubmonoid.units

noncomputable def includeUnits (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) : (v.adicCompletion K)ˣ →* (L ⊗[K] v.adicCompletion K)ˣ :=
  Units.map
    (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom

open scoped TensorProduct.RightActions in

noncomputable def normOneUnits (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) : Subgroup (L ⊗[K] v.adicCompletion K)ˣ :=
  MonoidHom.ker
    ((Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))).toMonoidWithZeroHom.toMonoidHom.comp
      ((Algebra.norm (v.adicCompletion K) : L ⊗[K] v.adicCompletion K →* v.adicCompletion K).comp (Units.coeHom _)))

def saturatedUnits (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) : Set (L ⊗[K] v.adicCompletion K)ˣ :=
  (integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ) * Set.range (includeUnits K L v)

def valOneUnits (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) : Set (v.adicCompletion K)ˣ :=
  {s | Valued.v (s : v.adicCompletion K) = 1}

open scoped NumberField.LiesOver in
attribute [local instance] M4aHerbrand.ArchSemilocal.extLiesOver in

noncomputable def includeArchUnits (K L : Type) [Field K] [Field L] [Algebra K L]
    (v : InfinitePlace K) : (v.Completion)ˣ →* (∀ w : v.Extension L, w.1.Completion)ˣ :=
  Units.map (algebraMap v.Completion (∀ w : v.Extension L, w.1.Completion)).toMonoidHom

open scoped NumberField.LiesOver in
attribute [local instance] M4aHerbrand.ArchSemilocal.extLiesOver in

noncomputable def archNormOneUnits (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    (v : InfinitePlace K) : Subgroup (∀ w : v.Extension L, w.1.Completion)ˣ :=
  MonoidHom.ker
    ((normHom : v.Completion →*₀ ℝ).toMonoidHom.comp
      ((Algebra.norm v.Completion : (∀ w : v.Extension L, w.1.Completion) →* v.Completion).comp (Units.coeHom _)))

noncomputable def archFibre (K L : Type) [Field K] [Field L] [Algebra K L]
    (v : InfinitePlace K) : (InfiniteAdeleRing L)ˣ →* (∀ w : v.Extension L, w.1.Completion)ˣ :=
  Units.map
    (RingHom.pi fun w : v.Extension L => Pi.evalRingHom (fun u : InfinitePlace L => u.Completion) w.1 :
      InfiniteAdeleRing L →+* (∀ w : v.Extension L, w.1.Completion)).toMonoidHom

end Definitions

section Borel

open scoped TensorProduct.RightActions in

@[reducible] noncomputable def semiLocalUnitsBorel (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) : MeasurableSpace (L ⊗[K] v.adicCompletion K)ˣ :=
  borel _

@[reducible] noncomputable def archUnitsBorel (K L : Type) [Field K] [Field L]
    [Algebra K L] (v : InfinitePlace K) : MeasurableSpace (∀ w : v.Extension L, w.1.Completion)ˣ :=
  borel _

end Borel

noncomputable def archSemiLocalIdele (K L : Type) [Field K] [Field L] [NumberField L]
    [Algebra K L] (v : InfinitePlace K) : (AdeleRing (𝓞 L) L)ˣ →* (∀ w : v.Extension L, w.1.Completion)ˣ :=
  (archFibre K L v).comp
    (Units.map (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)).toMonoidHom)

noncomputable def semiLocalIdele (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) : (AdeleRing (𝓞 L) L)ˣ →* (L ⊗[K] v.adicCompletion K)ˣ :=
  (Units.map (AutomorphicForm.semiLocalEval K L v).toMonoidHom).comp (NumberField.AdeleRing.finitePartUnits (𝓞 L) L)

noncomputable def idelesBaseChange (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] : (AdeleRing (𝓞 K) K)ˣ →* (AdeleRing (𝓞 L) L)ˣ :=
  Units.map (M4aHerbrand.Bridge.genuineβ K L).toMonoidHom

def saturated (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (Sτ : Finset (HeightOneSpectrum (𝓞 K))) : Set (AdeleRing (𝓞 L) L)ˣ :=
  {t | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sτ → semiLocalIdele K L v t ∈ saturatedUnits K L v}

noncomputable def valOneUnitsSubgroup (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    Subgroup (v.adicCompletion K)ˣ :=
  MonoidHom.ker
    ((Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))).toMonoidWithZeroHom.toMonoidHom.comp
      (Units.coeHom (v.adicCompletion K)))

def levelSubgroup {B α κ : Type*} [Group B] {A : α → Type*} [∀ a, Group (A a)] {G : κ → Type*}
    [∀ k, Group (G k)] (q : ∀ a, B →* A a) (NA : ∀ a, Subgroup (A a)) (p : ∀ k, B →* G k)
    (N U : ∀ k, Subgroup (G k)) (bad : Finset κ) : Subgroup B where
  carrier := {b | (∀ a, q a b ∈ NA a) ∧ (∀ k ∈ bad, p k b ∈ N k) ∧ ∀ k ∉ bad, p k b ∈ U k}
  one_mem' := ⟨fun a => by rw [map_one]; exact one_mem _, fun k _ => by rw [map_one]; exact one_mem _,
    fun k _ => by rw [map_one]; exact one_mem _⟩
  mul_mem' := fun {a b} ha hb =>
    ⟨fun i => by rw [map_mul]; exact mul_mem (ha.1 i) (hb.1 i),
      fun k hk => by rw [map_mul]; exact mul_mem (ha.2.1 k hk) (hb.2.1 k hk),
      fun k hk => by rw [map_mul]; exact mul_mem (ha.2.2 k hk) (hb.2.2 k hk)⟩
  inv_mem' := fun {a} ha =>
    ⟨fun i => by rw [map_inv]; exact inv_mem (ha.1 i), fun k hk => by rw [map_inv]; exact inv_mem (ha.2.1 k hk),
      fun k hk => by rw [map_inv]; exact inv_mem (ha.2.2 k hk)⟩

section Boxes

attribute [local instance] semiLocalUnitsBorel archUnitsBorel

def IsBox (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (E : Set (AdeleRing (𝓞 L) L)ˣ) : Prop :=
  ∃ (D : ∀ v : InfinitePlace K, Set (∀ w : v.Extension L, w.1.Completion)ˣ)
    (C : ∀ v : HeightOneSpectrum (𝓞 K), Set (L ⊗[K] v.adicCompletion K)ˣ),
    (∀ v, MeasurableSet (D v)) ∧ (∀ v, MeasurableSet (C v)) ∧
      {v | C v ≠ (TransversalMeasure.integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ)}.Finite ∧
      E = {t | (∀ v, TransversalMeasure.archSemiLocalIdele K L v t ∈ D v) ∧
        ∀ v, TransversalMeasure.semiLocalIdele K L v t ∈ C v}

end Boxes

end AutomorphicForm.TransversalMeasure

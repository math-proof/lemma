module

public import Def.UnramifiedWhittaker_ZetaIntegrand
public import Theorem.AdelicDock_LocalEmbedding
public import Theorem.Set.IdeleBox

@[expose] public section

set_option autoImplicit false

open IsDedekindDomain NumberField Matrix.AdelicLevel NumberField.AdeleRing Matrix

noncomputable section

namespace NumberField.Idele

variable (F : Type) [Field F] [NumberField F]

def ord (v : HeightOneSpectrum (𝓞 F)) (a : (AdeleRing (𝓞 F) F)ˣ) : ℤ :=
  -WithZero.log (Valued.v ((a : AdeleRing (𝓞 F) F).2 v))

def unitComponent (v : HeightOneSpectrum (𝓞 F)) (a : (AdeleRing (𝓞 F) F)ˣ) : v.adicCompletion F :=
  (a : AdeleRing (𝓞 F) F).2 v *
    ((uniformizerUnit F v : (v.adicCompletion F)ˣ) : v.adicCompletion F) ^ (-(ord F v a))

open scoped Classical in

def truncFin (S : Finset (HeightOneSpectrum (𝓞 F))) :
    FiniteAdeleRing (𝓞 F) F →* FiniteAdeleRing (𝓞 F) F where
  toFun x := ⟨fun v => if v ∈ S then x v else 1, x.2.mono fun v hv => by
      show (if v ∈ S then x v else 1) ∈ v.adicCompletionIntegers F
      split_ifs
      · exact hv
      · exact one_mem _⟩
  map_one' := by
    refine Subtype.ext (funext fun v => ?_)
    show (if v ∈ S then (1 : FiniteAdeleRing (𝓞 F) F) v else 1) = (1 : FiniteAdeleRing (𝓞 F) F) v
    split_ifs <;> rfl
  map_mul' x y := by
    refine Subtype.ext (funext fun v => ?_)
    show (if v ∈ S then (x * y) v else 1) =
      (if v ∈ S then x v else 1) * (if v ∈ S then y v else 1)
    split_ifs
    · rfl
    · exact (one_mul (1 : v.adicCompletion F)).symm

def partAtAdele (S : Finset (HeightOneSpectrum (𝓞 F))) : AdeleRing (𝓞 F) F →* AdeleRing (𝓞 F) F where
  toFun a := (a.1, truncFin F S a.2)
  map_one' := Prod.ext rfl (map_one (truncFin F S))
  map_mul' a b := Prod.ext rfl (map_mul (truncFin F S) a.2 b.2)

def partAt (S : Finset (HeightOneSpectrum (𝓞 F))) : (AdeleRing (𝓞 F) F)ˣ →* (AdeleRing (𝓞 F) F)ˣ :=
  Units.map (partAtAdele F S)

open scoped Classical in

def unitFin (S : Finset (HeightOneSpectrum (𝓞 F))) (a : (AdeleRing (𝓞 F) F)ˣ) :
    (FiniteAdeleRing (𝓞 F) F)ˣ where
  val := ⟨fun v => if v ∈ S then 1 else unitComponent F v a, Filter.Eventually.of_forall fun v => by
      show (if v ∈ S then (1 : v.adicCompletion F) else unitComponent F v a) ∈ v.adicCompletionIntegers F
      split_ifs
      · exact one_mem _
      · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
        exact (valued_unitComponent F v a).le⟩
  inv := ⟨fun v => if v ∈ S then 1 else unitComponent F v a⁻¹, Filter.Eventually.of_forall fun v => by
      show (if v ∈ S then (1 : v.adicCompletion F) else unitComponent F v a⁻¹) ∈
        v.adicCompletionIntegers F
      split_ifs
      · exact one_mem _
      · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
        exact (valued_unitComponent F v a⁻¹).le⟩
  val_inv := by
    refine Subtype.ext (funext fun v => ?_)
    show (if v ∈ S then (1 : v.adicCompletion F) else unitComponent F v a) *
        (if v ∈ S then (1 : v.adicCompletion F) else unitComponent F v a⁻¹) = 1
    split_ifs
    · exact one_mul 1
    · exact unitComponent_mul_unitComponent_inv F v a
  inv_val := by
    refine Subtype.ext (funext fun v => ?_)
    show (if v ∈ S then (1 : v.adicCompletion F) else unitComponent F v a⁻¹) *
        (if v ∈ S then (1 : v.adicCompletion F) else unitComponent F v a) = 1
    split_ifs
    · exact one_mul 1
    · rw [mul_comm]
      exact unitComponent_mul_unitComponent_inv F v a

def unitPart (S : Finset (HeightOneSpectrum (𝓞 F))) (a : (AdeleRing (𝓞 F) F)ˣ) : (AdeleRing (𝓞 F) F)ˣ :=
  Units.map (finIncl (𝓞 F) F) (unitFin F S a)

end NumberField.Idele

namespace NumberField.Idele

open MeasureTheory

variable (F : Type) [Field F] [NumberField F]

attribute [local instance] ideleBorel borelSpace_ideleBorel

def idelicHaar : Measure (AdeleRing (𝓞 F) F)ˣ := Measure.haar

open scoped Classical in

open scoped Classical in

def sPartMeasure (S : Finset (HeightOneSpectrum (𝓞 F))) : Measure (AdeleRing (𝓞 F) F)ˣ :=
  Measure.map (partAt F S)
    ((idelicHaar F).restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S) : Set (AdeleRing (𝓞 F) F)ˣ))

private def ordHom (v : HeightOneSpectrum (𝓞 F)) : (AdeleRing (𝓞 F) F)ˣ →* Multiplicative ℤ where
  toFun a := Multiplicative.ofAdd (ord F v a)
  map_one' := by rw [ord_one]; rfl
  map_mul' a b := by rw [ord_mul]; rfl

def productMeasureData (S : Finset (HeightOneSpectrum (𝓞 F))) :
    @UnramifiedWhittaker.ProductMeasureData F _ _ (ideleBorel F) S (idelicHaar F) where
  c := 1
  c_pos := one_pos
  νS := sPartMeasure F S
  projS := partAt F S
  ord := ord F
  projS_off a _ hv := partAt_snd_of_not_mem F S a hv
  decomp L hLS hL a ha := ⟨unitPart F S a, unitPart_fst F S a, unitPart_snd_of_mem F S a,
    finitePartUnits_unitPart_mem_unitIdeles F S a, eq_partAt_mul_prod_mul_unitPart F S L hLS hL a ha⟩
  tonelli L hLS hL f φ hf hφ := by
    obtain ⟨h1, h2⟩ := integrableOn_and_integral_eq F S f φ hf L hLS hL hφ
    exact ⟨h1, by rw [h2, Complex.ofReal_one, one_mul]⟩
  measurableSet L _ _ := (isOpen_unitIdelesOutside F _).measurableSet

end NumberField.Idele

end

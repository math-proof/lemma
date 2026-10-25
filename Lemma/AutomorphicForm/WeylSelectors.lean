import Def.NumberField_AdelicBox
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Structure.AutomorphicForm_WeylSelectors
import Notation.AutomorphicForm_WeylSelectors

noncomputable section

open MeasureTheory NumberField NumberField.AdelicBox IsDedekindDomain
open scoped Classical Pointwise

namespace AutomorphicForm.WeylIntegrable

section Generic

variable {A : Type*} [CommRing A] {ε y z x : A}


def yUnit (h : SelRel ε y z x) : Aˣ :=
  ⟨y, ε * z + (1 - ε), by linear_combination ε * h.yz + h.small, by linear_combination ε * h.yz + h.small⟩

@[simp] theorem coe_yUnit (h : SelRel ε y z x) : (yUnit h : A) = y := rfl
theorem coe_yUnit_inv (h : SelRel ε y z x) : (((yUnit h)⁻¹ : Aˣ) : A) = ε * z + (1 - ε) := rfl

end Generic

section Adelic

variable (F : Type) [Field F] [NumberField F]

open scoped AutomorphicForm_WeylSelectors

def toAdele' (a : 𝔸∞) (b : 𝔸f) : 𝔸 := (a, b)

def finOfIntegral (f : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F)
    (hf : ∀ v, f v ∈ v.adicCompletionIntegers F) : 𝔸f :=
  show RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite from
    RestrictedProduct.mk f (.of_forall hf)

@[simp] theorem finOfIntegral_apply (f : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F)
    (hf : ∀ v, f v ∈ v.adicCompletionIntegers F) (v : HeightOneSpectrum (𝓞 F)) : finOfIntegral F f hf v = f v := rfl

def BigInf (a : 𝔸∞) (w : InfinitePlace F) : Prop := 1 < ‖a w‖

def BigFin (b : 𝔸f) (v : HeightOneSpectrum (𝓞 F)) : Prop := b v ∉ v.adicCompletionIntegers F

omit [NumberField F] in
theorem ne_zero_of_bigInf {a : 𝔸∞} {w : InfinitePlace F} (h : BigInf F a w) : a w ≠ 0 := by
  intro h0; rw [BigInf, h0, norm_zero] at h; exact (not_lt.mpr zero_le_one) h

theorem one_lt_valued_of_bigFin {b : 𝔸f} {v : HeightOneSpectrum (𝓞 F)} (h : BigFin F b v) : 1 < Valued.v (b v) := by
  rw [BigFin, HeightOneSpectrum.mem_adicCompletionIntegers, not_le] at h; exact h

theorem ne_zero_of_bigFin {b : 𝔸f} {v : HeightOneSpectrum (𝓞 F)} (h : BigFin F b v) : b v ≠ 0 := by
  intro h0; have := one_lt_valued_of_bigFin F h; rw [h0, map_zero] at this; exact (not_lt.mpr zero_le_one) this

theorem inv_mem_of_bigFin {b : 𝔸f} {v : HeightOneSpectrum (𝓞 F)} (h : BigFin F b v) : (b v)⁻¹ ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  exact ((Valuation.one_lt_val_iff _ (ne_zero_of_bigFin F h)).mp (one_lt_valued_of_bigFin F h)).le

def selE (a : 𝔸∞) (b : 𝔸f) : 𝔸 := toAdele' F (fun w => if BigInf F a w then 1 else 0)
  (finOfIntegral F (fun v => if BigFin F b v then 1 else 0) fun v => by split_ifs <;> simp [one_mem, zero_mem])

def selZ (a : 𝔸∞) (b : 𝔸f) : 𝔸 := toAdele' F (fun w => if BigInf F a w then (a w)⁻¹ else 1)
  (finOfIntegral F (fun v => if BigFin F b v then (b v)⁻¹ else 1) fun v => by
    split_ifs with h
    · exact inv_mem_of_bigFin F h
    · exact one_mem _)

def selY (a : 𝔸∞) (b : 𝔸f) : 𝔸 := toAdele' F (fun w => if BigInf F a w then a w else 1)
  (show RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite from
    RestrictedProduct.mk (fun v => if BigFin F b v then b v else 1)
      ((show RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
          (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite from b).eventually.mono
        fun v hv => by
          rw [if_neg (show ¬ BigFin F b v from not_not.mpr hv)]
          exact one_mem _))

theorem selE_fst (a : 𝔸∞) (b : 𝔸f) (w : InfinitePlace F) : (selE F a b).1 w = if BigInf F a w then 1 else 0 := rfl
theorem selE_snd (a : 𝔸∞) (b : 𝔸f) (v : HeightOneSpectrum (𝓞 F)) : (selE F a b).2 v = if BigFin F b v then 1 else 0 := rfl
theorem selY_fst (a : 𝔸∞) (b : 𝔸f) (w : InfinitePlace F) : (selY F a b).1 w = if BigInf F a w then a w else 1 := rfl
theorem selY_snd (a : 𝔸∞) (b : 𝔸f) (v : HeightOneSpectrum (𝓞 F)) : (selY F a b).2 v = if BigFin F b v then b v else 1 := rfl
theorem selZ_fst (a : 𝔸∞) (b : 𝔸f) (w : InfinitePlace F) : (selZ F a b).1 w = if BigInf F a w then (a w)⁻¹ else 1 := rfl
theorem selZ_snd (a : 𝔸∞) (b : 𝔸f) (v : HeightOneSpectrum (𝓞 F)) : (selZ F a b).2 v = if BigFin F b v then (b v)⁻¹ else 1 := rfl
theorem toAdele'_fst (a : 𝔸∞) (b : 𝔸f) : (toAdele' F a b).1 = a := rfl
theorem toAdele'_snd (a : 𝔸∞) (b : 𝔸f) : (toAdele' F a b).2 = b := rfl

theorem mul_fst_apply (u u' : 𝔸) (w : InfinitePlace F) : (u * u').1 w = u.1 w * u'.1 w := rfl
theorem mul_snd_apply (u u' : 𝔸) (v : HeightOneSpectrum (𝓞 F)) : (u * u').2 v = u.2 v * u'.2 v := rfl
theorem sub_fst_apply (u u' : 𝔸) (w : InfinitePlace F) : (u - u').1 w = u.1 w - u'.1 w := rfl
theorem sub_snd_apply (u u' : 𝔸) (v : HeightOneSpectrum (𝓞 F)) : (u - u').2 v = u.2 v - u'.2 v := rfl
theorem one_fst_apply (w : InfinitePlace F) : (1 : 𝔸).1 w = 1 := rfl
theorem one_snd_apply (v : HeightOneSpectrum (𝓞 F)) : (1 : 𝔸).2 v = 1 := rfl

theorem adele_ext {u u' : 𝔸} (h1 : ∀ w, u.1 w = u'.1 w) (h2 : ∀ v, u.2 v = u'.2 v) : u = u' :=
  Prod.ext (funext h1) (Subtype.ext (funext h2))

theorem selRel (a : 𝔸∞) (b : 𝔸f) : SelRel (selE F a b) (selY F a b) (selZ F a b) (toAdele' F a b) where
  idem := adele_ext F (fun w => by rw [mul_fst_apply, selE_fst]; split_ifs <;> simp)
    (fun v => by rw [mul_snd_apply, selE_snd]; split_ifs <;> simp)
  yz := adele_ext F
    (fun w => by
      rw [mul_fst_apply, selY_fst, selZ_fst, one_fst_apply]
      split_ifs with h
      · exact mul_inv_cancel₀ (ne_zero_of_bigInf F h)
      · exact mul_one 1)
    (fun v => by
      rw [mul_snd_apply, selY_snd, selZ_snd, one_snd_apply]
      split_ifs with h
      · exact mul_inv_cancel₀ (ne_zero_of_bigFin F h)
      · exact mul_one 1)
  small := adele_ext F
    (fun w => by rw [mul_fst_apply, sub_fst_apply, one_fst_apply, selE_fst, selY_fst]; split_ifs <;> simp)
    (fun v => by rw [mul_snd_apply, sub_snd_apply, one_snd_apply, selE_snd, selY_snd]; split_ifs <;> simp)
  big := adele_ext F
    (fun w => by rw [mul_fst_apply, mul_fst_apply, selE_fst, selY_fst, toAdele'_fst]; split_ifs <;> simp)
    (fun v => by rw [mul_snd_apply, mul_snd_apply, selE_snd, selY_snd, toAdele'_snd]; split_ifs <;> simp)

end Adelic

section Lattice

variable (F : Type) [Field F] [NumberField F]

open scoped AutomorphicForm_WeylSelectors

def intLattice : AddSubgroup 𝔸f where
  carrier := integralFiniteAdeles (𝓞 F) F
  zero_mem' := fun _ => zero_mem _
  add_mem' hx hy := fun v => add_mem (hx v) (hy v)
  neg_mem' hx := fun v => neg_mem (hx v)

@[simp] theorem coe_intLattice : (intLattice F : Set 𝔸f) = integralFiniteAdeles (𝓞 F) F := rfl

def dilate (y : (𝔸f)ˣ) : AddSubgroup 𝔸f := (intLattice F).map (DistribSMul.toAddMonoidHom 𝔸f (y : 𝔸f))

theorem coe_dilate (y : (𝔸f)ˣ) : (dilate F y : Set 𝔸f) = (y : 𝔸f) • integralFiniteAdeles (𝓞 F) F := by
  ext z; simp [dilate, Set.mem_smul_set]

theorem snd_mul (x y : 𝔸) : (x * y).2 = x.2 * y.2 := rfl

def finPart (Y : (𝔸)ˣ) : (𝔸f)ˣ where
  val := (Y : 𝔸).2
  inv := ((Y⁻¹ : (𝔸)ˣ) : 𝔸).2
  val_inv := by rw [← snd_mul, Units.mul_inv]; rfl
  inv_val := by rw [← snd_mul, Units.inv_mul]; rfl

end Lattice

section Modulus

variable (F : Type) [Field F] [NumberField F]

open scoped AutomorphicForm_WeylSelectors

def Dy (x : 𝔸) : ℝ := (distribHaarChar 𝔸 (yUnit (selRel F x.1 x.2)) : ℝ)

end Modulus

end AutomorphicForm.WeylIntegrable

end

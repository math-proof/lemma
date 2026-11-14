import Def.NumberField_AdelicVolume
import Lemma.Matrix.AdelicLevel

open MeasureTheory Set IsDedekindDomain NumberField
open scoped ENNReal

noncomputable section

namespace NumberField.AdelicVolume

section Adelic

open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField.AdelicLevel

variable (F : Type) [Field F] [NumberField F]
variable {F}

open scoped Classical in
theorem archCentralUnit_snd (v₀ : InfinitePlace F) (a : (v₀.Completion)ˣ) :
    ((archCentralUnit F v₀ a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1 :=
  rfl

open scoped Classical in
theorem archCentralUnit_fst_self (v₀ : InfinitePlace F) (a : (v₀.Completion)ˣ) :
    ((archCentralUnit F v₀ a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 v₀ = a := by
  change Function.update (1 : InfiniteAdeleRing F) v₀ (a : v₀.Completion) v₀ = a
  rw [Function.update_self]

open scoped Classical in
theorem archCentralUnit_fst_of_ne (v₀ : InfinitePlace F) (a : (v₀.Completion)ˣ)
    {v : InfinitePlace F} (hv : v ≠ v₀) :
    ((archCentralUnit F v₀ a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 v = 1 := by
  change Function.update (1 : InfiniteAdeleRing F) v₀ (a : v₀.Completion) v = 1
  rw [Function.update_of_ne hv]
  rfl

theorem archCentralUnit_fst_ne_zero (v₀ : InfinitePlace F) (a : (v₀.Completion)ˣ)
    (v : InfinitePlace F) :
    ((archCentralUnit F v₀ a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 v ≠ 0 := by
  by_cases hv : v = v₀
  · subst hv
    rw [archCentralUnit_fst_self]
    exact a.ne_zero
  · rw [archCentralUnit_fst_of_ne v₀ a hv]
    exact one_ne_zero

theorem centralScalar_val (w : (AdeleRing (𝓞 F) F)ˣ) :
    ((centralScalar (𝓞 F) F w : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = Matrix.diagonal fun _ => (w : AdeleRing (𝓞 F) F) := by
  show Matrix.scalar (Fin 2) (w : AdeleRing (𝓞 F) F) = _
  rw [Matrix.scalar_apply]

theorem centralScalar_apply_eq (w : (AdeleRing (𝓞 F) F)ˣ) (i : Fin 2) :
    ((centralScalar (𝓞 F) F w : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i i
      = (w : AdeleRing (𝓞 F) F) := by
  rw [centralScalar_val, Matrix.diagonal_apply_eq]

theorem centralScalar_apply_ne (w : (AdeleRing (𝓞 F) F)ˣ) {i j : Fin 2} (h : i ≠ j) :
    ((centralScalar (𝓞 F) F w : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j
      = 0 := by
  rw [centralScalar_val, Matrix.diagonal_apply_ne _ h]


omit [NumberField F] in
theorem norm_two_completion (v₀ : InfinitePlace F) : ‖(2 : v₀.Completion)‖ = 2 := by
  rw [← (InfinitePlace.Completion.isometry_extensionEmbedding v₀).norm_map_of_map_zero (map_zero _),
    map_ofNat, RCLike.norm_ofNat]

theorem continuous_archDetNorm (v₀ : InfinitePlace F) : Continuous (archDetNorm (F := F) v₀) :=
  continuous_norm.comp ((Units.continuous_val.comp
    ((continuous_archComponent F v₀).comp (continuous_glArch (𝓞 F) F))).matrix_det)

theorem archDetNorm_pos (v₀ : InfinitePlace F) (g : AdelicGL2 (𝓞 F) F) : 0 < archDetNorm v₀ g :=
  norm_pos_iff.mpr (Matrix.GeneralLinearGroup.det_ne_zero _)

theorem archDetNorm_centralScalar_mul (v₀ : InfinitePlace F) (a : (v₀.Completion)ˣ)
    (g : AdelicGL2 (𝓞 F) F) :
    archDetNorm v₀ (centralScalar (𝓞 F) F (archCentralUnit F v₀ a) * g)
      = (‖(a : v₀.Completion)‖ * ‖(a : v₀.Completion)‖) * archDetNorm v₀ g := by
  unfold archDetNorm
  rw [map_mul, map_mul, Units.val_mul, Matrix.det_mul, norm_mul]
  congr 1
  set s := archComponent F v₀ (glArch (𝓞 F) F (centralScalar (𝓞 F) F (archCentralUnit F v₀ a)))
  have hs : ∀ i j : Fin 2, (s : Matrix (Fin 2) (Fin 2) v₀.Completion) i j
      = if i = j then (a : v₀.Completion) else 0 := by
    intro i j
    simp only [s, archComponent_apply, glArch_apply]
    by_cases h : i = j
    · subst h
      rw [centralScalar_apply_eq, ite_eq_left rfl]
      exact archCentralUnit_fst_self v₀ a
    · rw [centralScalar_apply_ne _ h, ite_eq_right h]
      rfl
  rw [Matrix.det_fin_two, hs, hs, hs, hs]
  simp [norm_mul]

end Adelic

end NumberField.AdelicVolume

end

import Mathlib
import Instance.AlgebraicGeometry_ResolvedModelGlue
import Structure.AlgebraicGeometry_ResolvedModelGlue

set_option autoImplicit false
set_option maxHeartbeats 200000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace V3Glue


namespace GlueInput

variable {X : Scheme.{0}} {N : Type} (D : GlueInput X N)

def F₁ (n : N) : WidePushoutShape Bool ⥤ Scheme.{0} :=
  WidePushoutShape.wideSpan ((D.U n ⊓ D.X0 : X.Opens) : Scheme.{0})
    (fun b => Bool.casesOn b (D.Y n) ((D.X0 : X.Opens) : Scheme.{0}))
    (fun b => match b with
      | true => X.homOfLE inf_le_right
      | false => D.j n)

def Y'' (n : N) : Scheme.{0} := colimit (D.F₁ n)

def toX'' (n : N) : D.Y'' n ⟶ X :=
  colimit.desc (D.F₁ n) (WidePushoutShape.mkCocone ((D.U n ⊓ D.X0).ι)
    (fun b => match b with
      | true => D.X0.ι
      | false => D.q n ≫ (D.U n).ι)
    (by
      rintro (_ | _)
      · show D.j n ≫ D.q n ≫ (D.U n).ι = (D.U n ⊓ D.X0).ι
        rw [← Category.assoc, D.j_q, Scheme.homOfLE_ι]
      · show X.homOfLE inf_le_right ≫ D.X0.ι = (D.U n ⊓ D.X0).ι
        rw [Scheme.homOfLE_ι]))

def ιX0'' (n : N) : ((D.X0 : X.Opens) : Scheme.{0}) ⟶ D.Y'' n := colimit.ι (D.F₁ n) (some true)

def ιY'' (n : N) : D.Y n ⟶ D.Y'' n := colimit.ι (D.F₁ n) (some false)

def F₂ : WidePushoutShape N ⥤ Scheme.{0} :=
  WidePushoutShape.wideSpan ((D.X0 : X.Opens) : Scheme.{0}) (fun n => D.Y'' n) (fun n => D.ιX0'' n)

def glued : Scheme.{0} := colimit D.F₂

def toDR : D.glued ⟶ X :=
  colimit.desc D.F₂ (WidePushoutShape.mkCocone D.X0.ι (fun n => D.toX'' n) (fun n => D.ιX0''_toX'' n))

def ιX0 : ((D.X0 : X.Opens) : Scheme.{0}) ⟶ D.glued := colimit.ι D.F₂ none

def ιY''glued (n : N) : D.Y'' n ⟶ D.glued := colimit.ι D.F₂ (some n)

def ιY (n : N) : D.Y n ⟶ D.glued := D.ιY'' n ≫ D.ιY''glued n

def openCover : D.glued.OpenCover :=
  Scheme.Cover.mkOfCovers (Option N) (fun o => Option.casesOn o ((D.X0 : X.Opens) : Scheme.{0}) D.Y)
    (fun o => match o with
      | none => D.ιX0
      | some n => D.ιY n)
    (fun y => by
      rcases D.ι_jointly_surjective y with ⟨x0, hx0⟩ | ⟨n, yn, hyn⟩
      · exact ⟨none, x0, hx0⟩
      · exact ⟨some n, yn, hyn⟩)
    (by rintro (_ | n) <;> dsimp <;> infer_instance)

variable (hq : ∀ n (y : D.Y n), ((D.q n).base y).1 ∈ D.X0 → y ∈ Set.range (D.j n).base)
include hq

end GlueInput

end V3Glue

namespace V3Glue


namespace ChartInput

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)

def Y (n : N) : Scheme.{0} := pullback (C.f n) (C.ρ n)

def q (n : N) : C.Y n ⟶ (C.U n : X.Opens) := pullback.fst (C.f n) (C.ρ n)

abbrev a (n : N) : ((C.U n ⊓ C.X0 : X.Opens) : Scheme.{0}) ⟶ (C.U n : X.Opens) := X.homOfLE inf_le_left

def l (n : N) : ((C.U n ⊓ C.X0 : X.Opens) : Scheme.{0}) ⟶ (C.Vc n : Scheme.{0}) :=
  IsOpenImmersion.lift (C.Vc n).ι (C.a n ≫ C.f n) (C.range_a_f_subset n)

def j (n : N) : ((C.U n ⊓ C.X0 : X.Opens) : Scheme.{0}) ⟶ C.Y n :=
  inv (pullback.fst (C.a n) (C.q n)) ≫ pullback.snd (C.a n) (C.q n)

def toGlueInput : GlueInput X N where
  x := C.x
  X0 := C.X0
  mem_X0 := C.mem_X0
  U := C.U
  x_mem_U := C.x_mem_U
  x_not_mem_U := C.x_not_mem_U
  Y := C.Y
  q := C.q
  j := C.j
  j_isOpenImmersion := inferInstance
  j_q := C.j_q

def g (n : N) : C.Y n ⟶ C.Res n := pullback.snd (C.f n) (C.ρ n)

def toB (n : N) : C.Y n ⟶ C.B := C.g n ≫ C.ρ n ≫ C.σ n

end ChartInput


namespace RawChartInput

variable {X : Scheme.{0}} {N : Type} [Finite N] (R : RawChartInput X N)

def X0 : X.Opens := ⟨(⋃ n, ({R.x n} : Set X))ᶜ, (isClosed_iUnion_of_finite R.isClosed_x).isOpen_compl⟩

def avoid (n : N) : X.Opens :=
  ⟨(⋃ m : {m : N // m ≠ n}, ({R.x m.1} : Set X))ᶜ,
    (isClosed_iUnion_of_finite fun m : {m : N // m ≠ n} => R.isClosed_x m.1).isOpen_compl⟩

variable (hnbhd : ∀ n, ∃ V : ((R.U₀ n : X.Opens) : Scheme.{0}).Opens,
  (⟨R.x n, R.x_mem_U₀ n⟩ : R.U₀ n) ∈ V ∧ Etale (V.ι ≫ R.f₀ n))

def V (n : N) : ((R.U₀ n : X.Opens) : Scheme.{0}).Opens := (hnbhd n).choose

abbrev U₁ (n : N) : X.Opens := (R.U₀ n).ι ''ᵁ R.V hnbhd n

abbrev U (n : N) : X.Opens := R.U₁ hnbhd n ⊓ R.avoid n

def toChartInput : ChartInput X N where
  x := R.x
  X0 := R.X0
  mem_X0 := R.mem_X0
  S := R.S
  Vc := R.Vc
  Res := R.Res
  ρ := R.ρ
  isIso_ρ_restrict := inferInstance
  isProper_ρ := inferInstance
  thick := R.thick
  one_le_thick := R.one_le_thick
  U := R.U hnbhd
  x_mem_U := R.x_mem_U hnbhd
  x_not_mem_U n m hmn h := (R.mem_avoid n _).mp h.2 m hmn rfl
  f n := X.homOfLE (R.U_le hnbhd n) ≫ R.f₀ n
  f_mem_Vc_iff n y := by
    rw [Scheme.Hom.comp_base, TopCat.comp_app, R.f₀_mem_Vc_iff]
    have : ((X.homOfLE (R.U_le hnbhd n)).base y).1 = y.1 := by
      simpa using congr($(X.homOfLE_ι (R.U_le hnbhd n)).base y)
    exact Iff.of_eq (congrArg (fun z : X => z ≠ R.x n) this)
  f_etale n := R.etale_homOfLE_f₀ hnbhd n
  f_node n := R.node_homOfLE_f₀ hnbhd n ⟨R.x n, R.x_mem_U hnbhd n⟩ rfl
  B := R.B
  πX := R.πX
  σ := R.σ
  f_over n := by rw [Category.assoc, R.f₀_over, ← Category.assoc, Scheme.homOfLE_ι]
  flat_ρ_σ := inferInstance
  isLocallyNoetherian_Res := inferInstance
  interior_preimage_vertex := R.interior_preimage_vertex

omit [Finite N] in

end RawChartInput

end V3Glue

end

noncomputable section

namespace V3Glue.GlueInput

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

variable {X : Scheme.{0}} {N : Type} (D : GlueInput X N)

omit D in

variable (hq : ∀ n (y : D.Y n), ((D.q n).base y).1 ∈ D.X0 → y ∈ Set.range (D.j n).base)
include hq

end V3Glue.GlueInput

end

noncomputable section

namespace V3Glue.GlueInput

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

variable {X : Scheme.{0}} {N : Type} (D : GlueInput X N)

omit D in

variable (hq : ∀ n (y : D.Y n), ((D.q n).base y).1 ∈ D.X0 → y ∈ Set.range (D.j n).base)
include hq

end V3Glue.GlueInput

end

noncomputable section

namespace V3Glue.GlueInput

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

variable {X : Scheme.{0}} {N : Type} (D : GlueInput X N)
variable (hq : ∀ n (y : D.Y n), ((D.q n).base y).1 ∈ D.X0 → y ∈ Set.range (D.j n).base)
include hq

end V3Glue.GlueInput

end

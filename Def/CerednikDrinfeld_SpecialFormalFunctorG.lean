import Mathlib
import Lemma.MvFormalGroup.NegV2
import Lemma.CerednikDrinfeld.SpecialFormalModule
import Def.CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Structure.CerednikDrinfeld_SpecialFormalFunctorG

set_option autoImplicit false

noncomputable section

universe u v

namespace CerednikDrinfeld
namespace SpecialFormal

open FormalOmega

variable {p : ℕ} [Fact p.Prime]

namespace Rigidified

variable {O : Type v} [CommRing O] {Φ : FormalODModule p (O ⧸ pIdeal p O)}
variable {B : Type u} [CommRing B]

def frobSeries (B : Type u) [CommRing B] (j : ℕ) : Series B :=
  fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ (p ^ j)

def IsTranslate (e : Series (O ⧸ pIdeal p O)) (k m' : ℕ) (ψ : O →+* B) (t t' : Rigidified p Φ B) :
    Prop :=
  t'.X = t.X ∧
    ∃ c : ℕ,
      (t.Xbar.act ((p : Zp2 p) ^ (c + t.n + k))).comp (t'.ρ.comp (frobSeries (p := p) _ m')) =
        (t.Xbar.act ((p : Zp2 p) ^ (c + t'.n))).comp
          (t.ρ.comp ((Series.map (residueMap ψ) e).comp (frobSeries (p := p) _ (2 * k))))

def IsPiTranslate (ψ : O →+* B) (t t' : Rigidified p Φ B) : Prop :=
  t'.X.F = t.X.F ∧ t'.X.varpi = t.X.varpi ∧ (∀ a, t'.X.act a = t.X.act (WittVector.frobenius a)) ∧
    ∃ c : ℕ,
      (t.Xbar.act ((p : Zp2 p) ^ (c + t.n))).comp
          (t'.ρ.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal p B)) ^ p) =
        (t.Xbar.act ((p : Zp2 p) ^ (c + t'.n))).comp (t.ρ.comp (Φ.varpi.map (residueMap ψ)))

end Rigidified

namespace ModuliPackage

variable (𝒪 : Type) [CommRing 𝒪] {O : Type} [CommRing O] [Algebra 𝒪 O]


namespace GPoint

variable {𝒪}
variable {M : ModuliPackage.{0, 0} p O} {B : Type} [CommRing B] [Algebra 𝒪 B]

theorem ext' {x y : GPoint 𝒪 M B} (h₁ : x.ψ = y.ψ) (h₂ : HEq x.pt y.pt) : x = y := by
  obtain ⟨ψ, n, m⟩ := x
  obtain ⟨ψ', n', m'⟩ := y
  cases h₁
  cases h₂
  rfl

def map {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (φ : B →ₐ[𝒪] B') (x : GPoint 𝒪 M B) :
    GPoint 𝒪 M B' where
  ψ := φ.comp x.ψ
  nilp := by simpa only [map_natCast] using x.nilp.map (φ : B →+* B')
  pt := M.map x.nilp (by simpa only [map_natCast] using x.nilp.map (φ : B →+* B'))
    (φ : B →+* B') rfl x.pt

@[simp] theorem map_ψ {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (φ : B →ₐ[𝒪] B') (x : GPoint 𝒪 M B) :
    (x.map φ).ψ = φ.comp x.ψ := rfl

theorem map_pt {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (φ : B →ₐ[𝒪] B') (x : GPoint 𝒪 M B) :
    (x.map φ).pt = M.map x.nilp (x.map φ).nilp (φ : B →+* B') rfl x.pt := rfl

theorem map_id (x : GPoint 𝒪 M B) : x.map (AlgHom.id 𝒪 B) = x :=
  ext' (AlgHom.id_comp _) (heq_of_eq (M.map_id x.nilp x.pt))

theorem map_comp {B₂ : Type} [CommRing B₂] [Algebra 𝒪 B₂] {B₃ : Type} [CommRing B₃] [Algebra 𝒪 B₃]
    (f : B →ₐ[𝒪] B₂) (g : B₂ →ₐ[𝒪] B₃) (x : GPoint 𝒪 M B) :
    x.map (g.comp f) = (x.map f).map g :=
  ext' (AlgHom.comp_assoc _ _ _)
    (heq_of_eq (M.map_comp x.nilp (x.map f).nilp ((x.map f).map g).nilp (g : B₂ →+* B₃) (f : B →+* B₂)
      rfl rfl x.pt))

end GPoint

def G (M : ModuliPackage.{0, 0} p O) : AlgFunctor 𝒪 where
  obj B _ _ := GPoint 𝒪 M B
  map φ x := x.map φ
  map_id x := x.map_id
  map_comp f g x := x.map_comp f g

@[simp] theorem G_obj (M : ModuliPackage.{0, 0} p O) (B : Type) [CommRing B] [Algebra 𝒪 B] :
    (G 𝒪 M).obj B = GPoint 𝒪 M B := rfl

@[simp] theorem G_map (M : ModuliPackage.{0, 0} p O) {B : Type} [CommRing B] [Algebra 𝒪 B]
    {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (φ : B →ₐ[𝒪] B') (x : GPoint 𝒪 M B) :
    (G 𝒪 M).map φ x = x.map φ := rfl

namespace G

variable {𝒪}
variable {M : ModuliPackage.{0, 0} p O} (ι : Zp2 p →+* O) (Φ : FormalODModule p (O ⧸ pIdeal p O))
  (η : ∀ (B : Type) [CommRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)), Rigidified p Φ B → M.obj B ψ hB)
  (Fr : O ≃ₐ[𝒪] O)

def LocallyLifts {B : Type} [CommRing B] (ψ ψ' : O →+* B) (hB : IsNilpotent (p : B))
    (m : M.obj B ψ hB) (m' : M.obj B ψ' hB)
    (Rel : ∀ (L : Type) [CommRing L], (O →+* L) → Rigidified p Φ L → Rigidified p Φ L → Prop) : Prop :=
  ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
    ∀ (i : Fin n) (L : Type) [CommRing L] [Algebra B L] [IsLocalization.Away (f i) L]
      (hL : IsNilpotent (p : L)),
      ∃ t t' : Rigidified p Φ L,
        t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧ t'.IsAdmissible ι ((algebraMap B L).comp ψ') ∧
        η L ((algebraMap B L).comp ψ) hL t = M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m ∧
        η L ((algebraMap B L).comp ψ') hL t' = M.map (ψ' := (algebraMap B L).comp ψ') hB hL (algebraMap B L) rfl m' ∧
        Rel L ((algebraMap B L).comp ψ) t t'

def IsTranslate (e : Series (O ⧸ pIdeal p O)) (k m' : ℕ) {B : Type} [CommRing B] [Algebra 𝒪 B]
    (x x' : GPoint 𝒪 M B) : Prop :=
  x'.ψ = frobTwist O Fr ((m' : ℤ) - 2 * k) x.ψ ∧
    LocallyLifts ι Φ η (x.ψ : O →+* B) (x'.ψ : O →+* B) x.nilp x.pt x'.pt
      (fun _ _ χ t t' => Rigidified.IsTranslate e k m' χ t t')

def IsPiTranslate {B : Type} [CommRing B] [Algebra 𝒪 B] (x x' : GPoint 𝒪 M B) : Prop :=
  x'.ψ = frobTwist O Fr 1 x.ψ ∧
    LocallyLifts ι Φ η (x.ψ : O →+* B) (x'.ψ : O →+* B) x.nilp x.pt x'.pt
      (fun _ _ χ t t' => Rigidified.IsPiTranslate χ t t')

def IsActBy {K : Type} [Field K] [Algebra 𝒪 K]
    (E₀ : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) K)
    {B : Type} [CommRing B] [Algebra 𝒪 B] (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (x x' : GPoint 𝒪 M B) : Prop :=
  ∃ (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (k m' : ℕ),
    E₀ e = (p : K) ^ k • ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ∧
    FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (p ^ (2 * m')) ∧
    IsTranslate ι Φ η Fr (e : MvFormalGroup.End Φ.F).toPowerSeries k m' x x'

end G

end ModuliPackage

end SpecialFormal
end CerednikDrinfeld

end

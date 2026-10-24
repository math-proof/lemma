import Mathlib
import Lemma.Definitions.Def_LatticeTreeOrbital
import Lemma.Definitions.Def_CerednikDrinfeld_BruhatTitsTree

set_option autoImplicit false

namespace CerednikDrinfeld
namespace FormalOmega

structure AlgFunctor (𝒪 : Type) [CommRing 𝒪] : Type 1 where

  obj : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], Type

  map : ∀ {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B'],
    (B →ₐ[𝒪] B') → obj B → obj B'

  map_id : ∀ {B : Type} [CommRing B] [Algebra 𝒪 B] (x : obj B), map (AlgHom.id 𝒪 B) x = x

  map_comp : ∀ {B₁ : Type} [CommRing B₁] [Algebra 𝒪 B₁] {B₂ : Type} [CommRing B₂] [Algebra 𝒪 B₂]
    {B₃ : Type} [CommRing B₃] [Algebra 𝒪 B₃] (f : B₁ →ₐ[𝒪] B₂) (g : B₂ →ₐ[𝒪] B₃) (x : obj B₁),
    map (g.comp f) x = map g (map f x)

namespace AlgFunctor

variable {𝒪 : Type} [CommRing 𝒪]

structure NatTrans (F G : AlgFunctor 𝒪) : Type 1 where

  app : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], F.obj B → G.obj B

  naturality : ∀ {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B']
    (f : B →ₐ[𝒪] B') (x : F.obj B), app B' (F.map f x) = G.map f (app B x)

def NatTrans.id (F : AlgFunctor 𝒪) : NatTrans F F where
  app := fun _ _ _ x => x
  naturality _ _ := rfl

def NatTrans.comp {F G H : AlgFunctor 𝒪} (η : NatTrans F G) (θ : NatTrans G H) : NatTrans F H where
  app := fun B _ _ x => θ.app B (η.app B x)
  naturality f x := by rw [η.naturality, θ.naturality]

def NatTrans.IsIsoOnNilp (π : 𝒪) {F G : AlgFunctor 𝒪} (η : NatTrans F G) : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → Function.Bijective (η.app B)

def NatTrans.IsMonoOnNilp (π : 𝒪) {F G : AlgFunctor 𝒪} (η : NatTrans F G) : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → Function.Injective (η.app B)

def prod (F G : AlgFunctor 𝒪) : AlgFunctor 𝒪 where
  obj B := F.obj B × G.obj B
  map f x := (F.map f x.1, G.map f x.2)
  map_id x := by rw [F.map_id, G.map_id]
  map_comp f g x := by rw [F.map_comp, G.map_comp]

def corep (A : Type) [CommRing A] [Algebra 𝒪 A] : AlgFunctor 𝒪 where
  obj B := A →ₐ[𝒪] B
  map f ψ := f.comp ψ
  map_id _ := AlgHom.ext fun _ => rfl
  map_comp _ _ _ := AlgHom.ext fun _ => rfl

structure GroupAction (Γ : Type) [Group Γ] (F : AlgFunctor 𝒪) : Type 1 where

  act : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], Γ → F.obj B → F.obj B
  act_one : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (x : F.obj B), act B 1 x = x
  act_mul : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (g h : Γ) (x : F.obj B), act B (g * h) x = act B g (act B h x)

  act_map : ∀ {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B']
    (f : B →ₐ[𝒪] B') (g : Γ) (x : F.obj B), F.map f (act B g x) = act B' g (F.map f x)

end AlgFunctor

section Charts

variable (𝒪 : Type) [CommRing 𝒪]

def chartV (q : ℕ) : AlgFunctor 𝒪 where
  obj B := { ζ : B // IsUnit (ζ ^ q - ζ) }
  map f x := ⟨f x.1, by
    have h := x.2.map f
    rwa [map_sub, map_pow] at h⟩
  map_id _ := Subtype.ext rfl
  map_comp _ _ _ := Subtype.ext rfl

def chartE (π : 𝒪) (q : ℕ) : AlgFunctor 𝒪 where
  obj B := { p : B × B // p.1 * p.2 = algebraMap 𝒪 B π ∧ IsUnit (p.1 ^ (q - 1) - 1) ∧ IsUnit (p.2 ^ (q - 1) - 1) }
  map f x := ⟨(f x.1.1, f x.1.2), by
    obtain ⟨h₁, h₂, h₃⟩ := x.2
    refine ⟨?_, ?_, ?_⟩
    · rw [← map_mul, h₁, AlgHom.commutes]
    · have h := h₂.map f
      rwa [map_sub, map_pow, map_one] at h
    · have h := h₃.map f
      rwa [map_sub, map_pow, map_one] at h⟩
  map_id _ := Subtype.ext rfl
  map_comp _ _ _ := Subtype.ext rfl

def chartVUnit (q : ℕ) : AlgFunctor 𝒪 where
  obj B := { ζ : B // IsUnit (ζ ^ q - ζ) ∧ IsUnit ζ }
  map f x := ⟨f x.1, by
    obtain ⟨h₁, h₂⟩ := x.2
    refine ⟨?_, h₂.map f⟩
    have h := h₁.map f
    rwa [map_sub, map_pow] at h⟩
  map_id _ := Subtype.ext rfl
  map_comp _ _ _ := Subtype.ext rfl

def chartVUnitIncl (q : ℕ) : AlgFunctor.NatTrans (chartVUnit 𝒪 q) (chartV 𝒪 q) where
  app := fun _ _ _ x => ⟨x.1, x.2.1⟩
  naturality _ _ := Subtype.ext rfl

variable {𝒪}

theorem isUnit_pow_pred_sub_one_of_isUnit_pow_sub {B : Type} [CommRing B] {q : ℕ} (hq : 1 ≤ q) {ζ : B}
    (h : IsUnit (ζ ^ q - ζ)) : IsUnit (ζ ^ (q - 1) - 1) := by
  have hpow : ζ ^ q = ζ ^ (q - 1) * ζ := by
    rw [← pow_succ, Nat.sub_add_cancel hq]
  have hfac : ζ ^ q - ζ = ζ * (ζ ^ (q - 1) - 1) := by
    rw [hpow]; ring
  rw [hfac] at h
  exact isUnit_of_mul_isUnit_right h

theorem isUnit_pow_succ_sub_one_of_isNilpotent {B : Type} [CommRing B] {a : B} (ha : IsNilpotent a) (b : B) (n : ℕ) :
    IsUnit ((a * b) ^ (n + 1) - 1) := by
  have hab : IsNilpotent (a * b) := Commute.isNilpotent_mul_right (Commute.all a b) ha
  have hpow : IsNilpotent ((a * b) ^ (n + 1)) := by
    obtain ⟨m, hm⟩ := hab
    exact ⟨m, by rw [← pow_mul, Nat.mul_comm (n + 1) m, pow_mul, hm, zero_pow (Nat.succ_ne_zero n)]⟩
  exact hpow.isUnit_sub_one

noncomputable def vertexToEdge (π : 𝒪) {q : ℕ} (hq : 2 ≤ q) (B : Type) [CommRing B] [Algebra 𝒪 B]
    (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : (chartVUnit 𝒪 q).obj B) : (chartE 𝒪 π q).obj B :=
  ⟨(x.1, algebraMap 𝒪 B π * ↑(x.2.2.unit⁻¹)), by
    refine ⟨?_, ?_, ?_⟩
    ·
      calc x.1 * (algebraMap 𝒪 B π * ↑(x.2.2.unit⁻¹))
          = algebraMap 𝒪 B π * (x.1 * ↑(x.2.2.unit⁻¹)) := by ring
        _ = algebraMap 𝒪 B π := by rw [IsUnit.mul_val_inv, mul_one]
    · exact isUnit_pow_pred_sub_one_of_isUnit_pow_sub (le_trans (by norm_num) hq) x.2.1
    · obtain ⟨n, hn⟩ : ∃ n, q - 1 = n + 1 := ⟨q - 2, by omega⟩
      rw [hn]
      exact isUnit_pow_succ_sub_one_of_isNilpotent hB _ n⟩

theorem vertexToEdge_natural (π : 𝒪) {q : ℕ} (hq : 2 ≤ q) {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B']
    [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (f : B →ₐ[𝒪] B')
    (x : (chartVUnit 𝒪 q).obj B) :
    (chartE 𝒪 π q).map f (vertexToEdge π hq B hB x) = vertexToEdge π hq B' hB' ((chartVUnit 𝒪 q).map f x) := by
  apply Subtype.ext

  refine Prod.ext rfl ?_
  show f (algebraMap 𝒪 B π * ↑(x.2.2.unit⁻¹)) = algebraMap 𝒪 B' π * ↑(((chartVUnit 𝒪 q).map f x).2.2.unit⁻¹)
  rw [map_mul, AlgHom.commutes]
  congr 1
  have h1 : f x.1 * f ↑(x.2.2.unit⁻¹) = 1 := by
    rw [← map_mul, IsUnit.mul_val_inv, map_one]
  have h2 : f x.1 * ↑(((chartVUnit 𝒪 q).map f x).2.2.unit⁻¹) = 1 := by
    exact IsUnit.mul_val_inv _
  exact (IsUnit.mul_right_injective (x.2.2.map f)) (h1.trans h2.symm)

end Charts

section PadicInstance

variable (r : ℕ) [Fact r.Prime]

noncomputable abbrev padicChartV : AlgFunctor ℤ_[r] := chartV ℤ_[r] r

noncomputable abbrev padicChartE : AlgFunctor ℤ_[r] := chartE ℤ_[r] (r : ℤ_[r]) r

def SpecialFibreVertexChartShape : Prop :=
  ∀ (𝔽 : Type) [Field 𝔽] [Algebra ℤ_[r] 𝔽] [CharP 𝔽 r] (ζ : 𝔽),
    IsUnit (ζ ^ r - ζ) ↔ ∀ a : ZMod r, (ζ : 𝔽) ≠ (a.cast : 𝔽)

end PadicInstance

end FormalOmega
end CerednikDrinfeld

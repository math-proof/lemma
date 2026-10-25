import Mathlib
import Lemma.CerednikDrinfeld.SpecialFormalModule
import Def.CerednikDrinfeld_ModuliPackageDescent

set_option autoImplicit false

namespace CerednikDrinfeld

namespace SpecialFormal

namespace ModuliPackage

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O]

def fibre (F : ModuliPackage.{0, 0} p O) {B C : Type} [CommRing B] [CommRing C]
    {ψB : O →+* B} {ψC : O →+* C} (hC : IsNilpotent (p : C)) (hB : IsNilpotent (p : B))
    (g : C →+* B) (hg : g.comp ψC = ψB) (x : F.obj B ψB hB) : Set (F.obj C ψC hC) :=
  {x' | F.map hC hB g hg x' = x}

def pullbackRing {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B) : Subring (B' × B'') :=
  RingHom.eqLocus (φ'.comp (RingHom.fst B' B'')) (φ''.comp (RingHom.snd B' B''))

def pullbackStr {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B) (ψ' : O →+* B') (ψ'' : O →+* B'')
    (h : φ'.comp ψ' = φ''.comp ψ'') : O →+* pullbackRing φ' φ'' :=
  (RingHom.prod ψ' ψ'').codRestrict (pullbackRing φ' φ'') (fun o => by
    show φ' (ψ' o) = φ'' (ψ'' o)
    exact congrArg (fun f : O →+* B => f o) h)

def pullbackFst {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B) : pullbackRing φ' φ'' →+* B' :=
  (RingHom.fst B' B'').comp (pullbackRing φ' φ'').subtype

def pullbackSnd {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B) : pullbackRing φ' φ'' →+* B'' :=
  (RingHom.snd B' B'').comp (pullbackRing φ' φ'').subtype

theorem pullbackFst_comp_pullbackStr {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B) (ψ' : O →+* B') (ψ'' : O →+* B'')
    (h : φ'.comp ψ' = φ''.comp ψ'') : (pullbackFst φ' φ'').comp (pullbackStr φ' φ'' ψ' ψ'' h) = ψ' :=
  RingHom.ext fun _ => rfl

theorem pullbackSnd_comp_pullbackStr {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B) (ψ' : O →+* B') (ψ'' : O →+* B'')
    (h : φ'.comp ψ' = φ''.comp ψ'') : (pullbackSnd φ' φ'').comp (pullbackStr φ' φ'' ψ' ψ'' h) = ψ'' :=
  RingHom.ext fun _ => rfl

def IsFPExact (F : ModuliPackage.{0, 0} p O) : Prop :=
  ∀ (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B'']
    (ψ : O →+* B) (ψ' : O →+* B') (ψ'' : O →+* B'')
    (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (hB'' : IsNilpotent (p : B''))
    (φ' : B' →+* B) (φ'' : B'' →+* B) (hφ' : φ'.comp ψ' = ψ) (hφ'' : φ''.comp ψ'' = ψ)
    (_ : Function.Surjective φ') (_ : Function.Surjective φ'')
    (_ : IsNilpotent (RingHom.ker φ')) (_ : IsNilpotent (RingHom.ker φ''))
    (hP : IsNilpotent (p : pullbackRing φ' φ'')),
    ∀ (x' : F.obj B' ψ' hB') (x'' : F.obj B'' ψ'' hB''),
      F.map hB' hB φ' hφ' x' = F.map hB'' hB φ'' hφ'' x'' →
      ∃! z : F.obj (pullbackRing φ' φ'') (pullbackStr φ' φ'' ψ' ψ'' (hφ'.trans hφ''.symm)) hP,
        F.map hP hB' (pullbackFst φ' φ'') (pullbackFst_comp_pullbackStr φ' φ'' ψ' ψ'' _) z = x' ∧
        F.map hP hB'' (pullbackSnd φ' φ'') (pullbackSnd_comp_pullbackStr φ' φ'' ψ' ψ'' _) z = x''

def LiftsAlong {G H : ModuliPackage.{0, 0} p O} (ξ : Hom G H) : Prop :=
  ∀ (B B' : Type) [CommRing B] [CommRing B'] (ψ : O →+* B) (ψ' : O →+* B')
    (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B'))
    (φ : B' →+* B) (hφ : φ.comp ψ' = ψ) (_ : Function.Surjective φ)
    (_ : RingHom.ker φ * RingHom.ker φ = ⊥) (x : G.obj B ψ hB),
    (H.fibre hB' hB φ hφ (ξ.app B ψ hB x)).Nonempty → (G.fibre hB' hB φ hφ x).Nonempty

end ModuliPackage

end SpecialFormal

end CerednikDrinfeld

module

public import Def.AutomorphicForm_HeckeEigensystem
public import Def.AutomorphicForm_HeckeEigensystemMap

public section

open IsDedekindDomain NumberField

namespace AutomorphicForm

namespace HeckeEigensystem

variable {F : Type*} [Field F] [NumberField F] {R : Type*} [CommRing R]
  {S : Type*} [CommRing S]


@[simp] public theorem map_level (ι : R →+* S) (Φ : HeckeEigensystem F R) :
    (Φ.map ι).level = Φ.level := rfl

@[simp] public theorem map_a (ι : R →+* S) (Φ : HeckeEigensystem F R)
    (v : HeightOneSpectrum (𝓞 F)) : (Φ.map ι).a v = ι (Φ.a v) := rfl

@[simp] public theorem map_b (ι : R →+* S) (Φ : HeckeEigensystem F R)
    (v : HeightOneSpectrum (𝓞 F)) : (Φ.map ι).b v = ι (Φ.b v) := rfl

public theorem map_id (Φ : HeckeEigensystem F R) : Φ.map (RingHom.id R) = Φ := rfl

public theorem map_map {T : Type*} [CommRing T] (ι : R →+* S) (κ : S →+* T)
    (Φ : HeckeEigensystem F R) : (Φ.map ι).map κ = Φ.map (κ.comp ι) := rfl

public theorem map_twist (ι : R →+* S) (Φ : HeckeEigensystem F R)
    (χ : HeightOneSpectrum (𝓞 F) → R) :
    (Φ.twist χ).map ι = (Φ.map ι).twist fun v => ι (χ v) := by
  simp only [map, twist]
  congr 1 <;> funext v
  · exact map_mul ι (χ v) (Φ.a v)
  · rw [map_mul, map_pow]

public theorem AgreesAwayFromFinite.map {Φ Φ' : HeckeEigensystem F R}
    (h : AgreesAwayFromFinite Φ Φ') (ι : R →+* S) :
    AgreesAwayFromFinite (Φ.map ι) (Φ'.map ι) := by
  obtain ⟨S₀, hS₀⟩ := h
  exact ⟨S₀, fun v hv => ⟨congrArg ι (hS₀ v hv).1, congrArg ι (hS₀ v hv).2⟩⟩

end HeckeEigensystem

end AutomorphicForm

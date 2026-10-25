import Theorem.Algebra.AdicCompletion.PolynomialCompletion.Part8
import Def.Algebra.AdicCompletion.RingFunctoriality.Part3
set_option autoImplicit false


namespace AdicCompletion

universe u₀ u₁ u₂ u₃

variable {k : Type u₀} [CommRing k]

variable {R : Type u₁} {S : Type u₂} {T : Type u₃} [CommRing R] [CommRing S] [CommRing T]

variable [Algebra k R] [Algebra k S] [Algebra k T]

section Map

variable (I : Ideal R) (J : Ideal S) (f : R →ₐ[k] S)

@[simp]
theorem evalₐ_mapₐ (h : I.map f ≤ J) (n : ℕ) (x : AdicCompletion I R) :
    evalₐ J n (mapₐ I J f h x) = levelMapₐ I J f h n (evalₐ I n x) :=
  evalₐ_liftAlgHom J (mapₐAux I J f h) (factorₐ_comp_mapₐAux I J f h) n x

@[simp]
theorem mapₐ_of (h : I.map f ≤ J) (x : R) : mapₐ I J f h (of I R x) = of J S (f x) :=
  ext_evalₐ fun n => by rw [evalₐ_mapₐ, evalₐ_of, evalₐ_of, levelMapₐ_mk]

theorem mapₐ_congr {f g : R →ₐ[k] S} (hfg : f = g) (hf : I.map f ≤ J) (hg : I.map g ≤ J) :
    mapₐ I J f hf = mapₐ I J g hg := by
  subst hfg
  rfl

theorem mapₐ_id (hI : I.map (AlgHom.id k R) ≤ I) :
    mapₐ I I (AlgHom.id k R) hI = AlgHom.id k (AdicCompletion I R) :=
  AlgHom.ext fun x => ext_evalₐ fun n => by
    rw [evalₐ_mapₐ, levelMapₐ_id]
    rfl

theorem mapₐ_comp (h : I.map f ≤ J) (K : Ideal T) (g : S →ₐ[k] T) (hg : J.map g ≤ K)
    (hgf : I.map (g.comp f) ≤ K) :
    mapₐ I K (g.comp f) hgf = (mapₐ J K g hg).comp (mapₐ I J f h) :=
  AlgHom.ext fun x => ext_evalₐ fun n => by
    simp only [evalₐ_mapₐ, AlgHom.comp_apply]
    rw [levelMapₐ_comp I J f h K g hg hgf]

theorem map_comp_le (h : I.map f ≤ J) (K : Ideal T) (g : S →ₐ[k] T) (hg : J.map g ≤ K) :
    I.map (g.comp f) ≤ K := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  exact Ideal.mem_comap.mpr (hg (Ideal.mem_map_of_mem g (h (Ideal.mem_map_of_mem f hx))))

theorem mapₐ_comp_apply (h : I.map f ≤ J) (K : Ideal T) (g : S →ₐ[k] T) (hg : J.map g ≤ K)
    (x : AdicCompletion I R) :
    mapₐ J K g hg (mapₐ I J f h x) = mapₐ I K (g.comp f) (map_comp_le I J f h K g hg) x := by
  rw [mapₐ_comp I J f h K g hg]
  rfl

end Map
end AdicCompletion

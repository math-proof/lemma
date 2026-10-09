import Mathlib
import sympy.Basic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

/--
[AlgebraicGeometry_Scheme_Modules_exists_basicOpen_forall_exists_frame](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_basicOpen_forall_exists_frame.lean)
-/
@[path]
private lemma main
  [Finite ι]
  {R : Type u} [CommRing R]
  {X : Scheme.{u}}
  {f : X ⟶ Spec (.of R)} [UniversallyClosed f]
  {M : X.Modules}
  {m : ι → Γ(M, ⊤)}
  {𝔭 : PrimeSpectrum R}
-- given
  (hgen : ∀ x : X, f x = 𝔭 → ∃ (i : ι) (U : X.Opens), x ∈ U ∧ ∀ V : X.Opens, V ≤ U → Function.Bijective fun g : Γ(X, V) => g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (m i) : Γ(M, V))) :
-- imply
  ∃ g : R, g ∉ 𝔭.asIdeal ∧ ∀ x : X, f x ∈ PrimeSpectrum.basicOpen g →
      ∃ (i : ι) (U : X.Opens), x ∈ U ∧ ∀ V : X.Opens, V ≤ U →
        Function.Bijective fun g : Γ(X, V) => g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (m i) : Γ(M, V)) := by
-- proof
  classical

  let W : Set X := {x | ∃ (i : ι) (U : X.Opens), x ∈ U ∧ ∀ V : X.Opens, V ≤ U →
    Function.Bijective fun g : Γ(X, V) => g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (m i) : Γ(M, V))}
  have hW : IsOpen W := by
    rw [isOpen_iff_forall_mem_open]
    rintro x ⟨i, U, hxU, hU⟩
    exact ⟨U, fun y hy => ⟨i, U, hy, hU⟩, U.isOpen, hxU⟩
  let Z : Set (PrimeSpectrum R) := f.base '' Wᶜ
  have hZ : IsClosed Z := f.isClosedMap _ hW.isClosed_compl
  have h𝔭Z : 𝔭 ∈ Zᶜ := by
    rintro ⟨x, hx, hfx⟩
    exact hx (hgen x hfx)
  obtain ⟨_, ⟨g, rfl⟩, hg𝔭, hgZ⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open h𝔭Z hZ.isOpen_compl
  refine ⟨g, hg𝔭, fun x hx => ?_⟩
  by_contra hx'
  exact hgZ hx ⟨x, hx', rfl⟩


-- created on 2026-10-05

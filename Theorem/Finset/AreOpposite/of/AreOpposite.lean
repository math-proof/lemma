module

public import Mathlib
public import Def.v1.Atlas.Buildings.code.Building.Spherical

public section


/--
[areOpposite_symm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Spherical.lean)
-/
public theorem areOpposite_symm
  [DecidableEq V]
  {K : SimplicialComplex V}
  {C D : Finset V}
-- given
  (h : AreOpposite K C D) :
-- imply
  AreOpposite K D C := by
-- proof
  obtain ⟨hC, hD, hmax⟩ := h
  refine ⟨hD, hC, fun C' D' hC' hD' => ?_⟩
  rw [galleryDist_comm K D C]
  exact hmax C' D' hC' hD'

public theorem SimplicialComplex.mem_chambers_iff
  [DecidableEq V]
  {K : SimplicialComplex V}
  {C : Finset V} :
-- imply
  C ∈ K.chambers ↔ K.IsMaximal C :=
-- proof
  Iff.rfl

public theorem SimplicialComplex.chambers_subset_faces
  [DecidableEq V]
  {K : SimplicialComplex V} :
-- imply
  K.chambers ⊆ K.faces := by
-- proof
  intro C hC
  exact ((K.mem_chambers_iff C).mp hC).1

public theorem Building.IsSpherical.finite_chambers
  [DecidableEq V]
  {b : Building V}
  {A : SimplicialComplex V}
-- given
  (hsph : b.IsSpherical)
  (hA : A ∈ b.apartmentSystem.apartments) :
-- imply
  Set.Finite (A.chambers) := by
-- proof
  apply Set.Finite.subset (hsph A hA)
  exact A.chambers_subset_faces


-- created on 2026-10-24

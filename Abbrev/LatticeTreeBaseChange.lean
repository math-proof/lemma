import Structure.LatticeTreeOrbital
import Structure.LatticeTreeBaseChange

set_option autoImplicit false

open scoped Matrix

namespace LT.LatticeTree

attribute [local simp] IntegralAut.symm_toBase IntegralAut.symm_toField galVec_galVec_symm galVec_symm_galVec
  latticeGal_latticeGal_symm latticeGal_symm_latticeGal latticeMap_one mem_fixedVertexSet mem_stdLattice
  mem_twistedFixedVertexSet

section BaseChangeVocabulary


section BaseChange

variable {R' : Type*} [CommRing R'] {K' : Type*} [Field K'] [Algebra R' K']
variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
variable (ι : IntegralHom R' K' R K)

abbrev IntegralHom.mapGL : Matrix.GeneralLinearGroup (Fin 2) K' →* Matrix.GeneralLinearGroup (Fin 2) K :=
  Matrix.GeneralLinearGroup.map ι.toField

end BaseChange

section Inhabitants

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

end Inhabitants

section Monotone

variable {R' : Type*} [CommRing R'] {K' : Type*} [Field K'] [Algebra R' K']
variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
variable (ι : IntegralHom R' K' R K)

end Monotone

section DepthCurrency

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

end DepthCurrency

section DepthBaseChange

variable {R' : Type*} [CommRing R'] {K' : Type*} [Field K'] [Algebra R' K']
variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
variable (ι : IntegralHom R' K' R K)

end DepthBaseChange

section DepthOrbital

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

end DepthOrbital

end BaseChangeVocabulary

end LT.LatticeTree

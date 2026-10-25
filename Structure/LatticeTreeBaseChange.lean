import Structure.LatticeTreeOrbital

set_option autoImplicit false

open scoped Matrix

namespace LT.LatticeTree


section BaseChangeVocabulary

structure IntegralHom (R' K' R K : Type*) [CommRing R'] [Field K'] [Algebra R' K']
    [CommRing R] [Field K] [Algebra R K] where

  toField : K' →+* K

  toBase : R' →+* R

  commutes : ∀ r : R', toField (algebraMap R' K' r) = algebraMap R K (toBase r)

section BaseChange

variable {R' : Type*} [CommRing R'] {K' : Type*} [Field K'] [Algebra R' K']
variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
variable (ι : IntegralHom R' K' R K)


end BaseChange

section Inhabitants

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

variable (R K) in


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

module

public import RingedSpaces

/-! # Clients of the non-affine constant-closed ringed-morphism theorem -/

set_option warningAsError true

@[expose] public section

namespace Test.ClosedPointNonAffine

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.RingedSpace.ClosedPointHom

universe u

variable {R K : Type u} [CommRing R] [IsLocalRing R] [Field K]

example (alpha : R →+* K) (r : R) (hr : r ∈ IsLocalRing.maximalIdeal R)
    (hne : alpha r ≠ 0) (beta : R →+* K) :
    hom R (Spec.sheafedSpaceObj (CommRingCat.of K))
        (CommRingCat.ofHom alpha ≫
          (StructureSheaf.globalSectionsIso (CommRingCat.of K)).hom).hom ≠
      Spec.sheafedSpaceMap (CommRingCat.ofHom beta) :=
  hom_ne_sheafedSpaceMap_of_isUnit alpha r hr (isUnit_iff_ne_zero.mpr hne) beta

example (alphaField : R →+* K) (r : R) (hr : r ∈ IsLocalRing.maximalIdeal R)
    (hne : alphaField r ≠ 0) (beta : R →+* K × K) :
    hom R (Spec.sheafedSpaceObj (CommRingCat.of (K × K)))
        (CommRingCat.ofHom (RingHom.prod alphaField alphaField) ≫
          (StructureSheaf.globalSectionsIso (CommRingCat.of (K × K))).hom).hom ≠
      Spec.sheafedSpaceMap (CommRingCat.ofHom beta) := by
  have hu : IsUnit ((RingHom.prod alphaField alphaField) r) := by
    rw [RingHom.prod_apply, Prod.isUnit_iff]
    exact ⟨isUnit_iff_ne_zero.mpr hne, isUnit_iff_ne_zero.mpr hne⟩
  exact hom_ne_sheafedSpaceMap_of_isUnit (RingHom.prod alphaField alphaField) r hr hu beta

end Test.ClosedPointNonAffine

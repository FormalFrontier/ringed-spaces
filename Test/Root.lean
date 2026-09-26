/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import RingedSpaces

/-!
# Aggregate-import client
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Test.Root

universe u

/-- A downstream client needs only the aggregate import for the full universal property. -/
theorem gluing {X Y : RingedSpace.{u, u}} (C : RingedSpace.OpenCover X)
    (f : ∀ i, C.obj i ⟶ Y)
    (hf : ∀ i j, pullback.fst (C.ι i) (C.ι j) ≫ f i =
      pullback.snd (C.ι i) (C.ι j) ≫ f j) :
    ∃! g : X ⟶ Y, ∀ i, C.ι i ≫ g = f i :=
  C.existsUnique_gluing f hf

/-- Aggregate-import client: both compatibility directions and unique literal gluing. -/
theorem literalGluing {X Y : RingedSpace.{u, u}} (C : RingedSpace.OpenCover X)
    (f : ∀ i, C.obj i ⟶ Y)
    (hf : ∀ i j, RingedSpace.restrictMap (C.U i ⊓ C.U j) (C.U i) inf_le_left ≫ f i =
      RingedSpace.restrictMap (C.U i ⊓ C.U j) (C.U j) inf_le_right ≫ f j) :
    ∃! g : X ⟶ Y, ∀ i, C.ι i ≫ g = f i := by
  have hpb := (C.pullback_compatibility_iff_intersection f).mpr hf
  have hlit := (C.pullback_compatibility_iff_intersection f).mp hpb
  exact C.existsUnique_gluing_of_intersection f hlit

end Test.Root

namespace Test.Root

/-- An aggregate-only client obtains the full factorization for every full morphism. -/
theorem inverseImageFull {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) :
    RingedSpace.toInverseImage f ≫ RingedSpace.ofInverseImage Y f.hom.base = f ∧
      (RingedSpace.toInverseImage f).hom.base = 𝟙 (X : TopCat) :=
  ⟨RingedSpace.toInverseImage_ofInverseImage f, RingedSpace.toInverseImage_base f⟩

/-- The aggregate also constructs the actual sheaf from an arbitrary continuous map. -/
theorem inverseImageContinuous (Y : RingedSpace.{u, u}) {T : TopCat.{u}}
    (g : T ⟶ Y.carrier) :
    (RingedSpace.inverseImage Y g).carrier = T ∧
      (RingedSpace.inverseImage Y g).sheaf =
        (TopCat.Sheaf.pullback CommRingCat.{u} g).obj Y.sheaf ∧
      (RingedSpace.ofInverseImage Y g).hom.base = g :=
  ⟨RingedSpace.inverseImage_carrier Y g, RingedSpace.inverseImage_sheaf Y g,
    RingedSpace.ofInverseImage_base Y g⟩

/-- The aggregate exposes both the full sheaf mate equation and every-open ring maps. -/
theorem inverseImageSections {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (U : (TopologicalSpace.Opens Y.carrier)ᵒᵖ) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).unit.app
        Y.sheaf ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map
        (RingedSpace.inverseImageMap f) =
        (CategoryTheory.Sheaf.homEquiv).symm f.hom.c ∧
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).unit.app
        Y.sheaf).hom.app U ≫
        ((TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map
          (RingedSpace.inverseImageMap f)).hom.app U = f.hom.c.app U :=
  ⟨RingedSpace.inverseImageMap_unit f, RingedSpace.inverseImageMap_unit_components f U⟩

end Test.Root

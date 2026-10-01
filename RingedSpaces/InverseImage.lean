/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Geometry.RingedSpace.Basic

/-!
# Inverse-image ringed spaces

For a ringed space `Y` and a continuous map `g : T ⟶ Y.carrier`, `inverseImage Y g`
has literal carrier `T` and the native inverse-image sheaf of commutative rings. Its
canonical map to `Y` is the unit of the inverse-image/pushforward adjunction.
Every full morphism `f : X ⟶ Y` factors through this object for `g = f.hom.base`:
the first map has identity base and the adjoint of the entire structure-sheaf map.

The construction is not a categorical fiber-product pullback. It uses diagonal
universes and does not require nonempty spaces, nonzero rings or local rings.

This standalone construction uses the native inverse-image sheaf and the adjunction
unit. It factors full ringed-space morphisms without a source-repository dependency.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Category CategoryTheory.Functor TopCat TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

variable (Y : RingedSpace.{u, u}) {T : TopCat.{u}} (g : T ⟶ Y.carrier)

/-- The ringed space on `T` with the native inverse-image sheaf of rings along `g`. -/
def inverseImage : RingedSpace.{u, u} where
  carrier := T
  presheaf := ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj Y.sheaf).1
  IsSheaf := ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj Y.sheaf).2

@[simp]
theorem inverseImage_carrier : (inverseImage Y g).carrier = T := rfl

@[simp]
theorem inverseImage_sheaf : (inverseImage Y g).sheaf =
    (TopCat.Sheaf.pullback CommRingCat.{u} g).obj Y.sheaf := rfl

/-- The canonical full ringed-space morphism induced by the sheaf adjunction unit. -/
def ofInverseImage : inverseImage Y g ⟶ Y :=
  InducedCategory.homMk
    { base := g
      c := ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g).unit.app
        Y.sheaf).hom }

@[simp]
theorem ofInverseImage_base : (ofInverseImage Y g).hom.base = g := rfl

@[simp]
theorem ofInverseImage_c : (ofInverseImage Y g).hom.c =
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g).unit.app Y.sheaf).hom :=
  rfl

theorem ofInverseImage_c_app (U : (Opens Y.carrier)ᵒᵖ) :
    (ofInverseImage Y g).hom.c.app U =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g).unit.app
        Y.sheaf).hom.app U := rfl

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The adjoint of the full structure-sheaf morphism of `f`, as a map of ring sheaves. -/
def inverseImageMap :
    (inverseImage Y f.hom.base).sheaf ⟶ X.sheaf :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).homEquiv
    Y.sheaf X.sheaf).symm ((CategoryTheory.Sheaf.homEquiv).symm f.hom.c)

/-- The mate equation as an equality of full ring-sheaf maps. -/
theorem inverseImageMap_unit :
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).unit.app
        Y.sheaf ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map (inverseImageMap f) =
      (CategoryTheory.Sheaf.homEquiv).symm f.hom.c := by
  change ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).homEquiv
    Y.sheaf X.sheaf) (inverseImageMap f) = (CategoryTheory.Sheaf.homEquiv).symm f.hom.c
  exact Equiv.apply_symm_apply _ _

/-- After forgetting to presheaves, the unit equation recovers the given structure map. -/
theorem inverseImageMap_unit_hom :
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).unit.app
        Y.sheaf ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map (inverseImageMap f)).hom =
      f.hom.c := by
  rw [inverseImageMap_unit]
  exact (CategoryTheory.Sheaf.homEquiv
    (X := Y.sheaf)
    (Y := (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj X.sheaf)).apply_symm_apply
      f.hom.c

/-- On every target open, the sheaf unit followed by the pushed-forward mate is `f`'s
ring map on sections. -/
theorem inverseImageMap_unit_app (U : (Opens Y.carrier)ᵒᵖ) :
    (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).unit.app
        Y.sheaf ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map (inverseImageMap f)).hom).app U =
      f.hom.c.app U :=
  congrArg (fun α => α.app U) (inverseImageMap_unit_hom f)

/-- The native unit and the pushed-forward mate compose as ring homomorphisms on every open. -/
theorem inverseImageMap_unit_components (U : (Opens Y.carrier)ᵒᵖ) :
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).unit.app
      Y.sheaf).hom.app U ≫
      ((TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map
        (inverseImageMap f)).hom.app U = f.hom.c.app U :=
  inverseImageMap_unit_app f U

/-- The full map from `X` to the inverse-image ringed space, over the identity of `X`. -/
def toInverseImage : X ⟶ inverseImage Y f.hom.base :=
  InducedCategory.homMk
    { base := 𝟙 (X : TopCat)
      c := (inverseImageMap f).hom ≫
        eqToHom (TopCat.Presheaf.Pushforward.id_eq X.presheaf).symm }

@[simp]
theorem toInverseImage_base : (toInverseImage f).hom.base = 𝟙 (X : TopCat) := rfl

/-- The first map's entire presheaf component includes the identity-pushforward transport. -/
theorem toInverseImage_c : (toInverseImage f).hom.c =
    (inverseImageMap f).hom ≫
      eqToHom (TopCat.Presheaf.Pushforward.id_eq X.presheaf).symm := rfl

theorem toInverseImage_c_app (U : (Opens X.carrier)ᵒᵖ) :
    (toInverseImage f).hom.c.app U =
      (inverseImageMap f).hom.app U ≫
        (eqToHom (TopCat.Presheaf.Pushforward.id_eq X.presheaf).symm).app U := rfl

/-- On sections, the identity-pushforward transport acts as the identity. -/
theorem toInverseImage_c_app_eq (U : (Opens X.carrier)ᵒᵖ) :
    (toInverseImage f).hom.c.app U = (inverseImageMap f).hom.app U := by
  rw [toInverseImage_c_app]
  rfl

/-- The two full morphisms compose to the original full morphism, including its sheaf map. -/
theorem toInverseImage_ofInverseImage :
    toInverseImage f ≫ ofInverseImage Y f.hom.base = f := by
  apply InducedCategory.hom_ext
  refine PresheafedSpace.hext _ _ (by rfl) ?_
  change (ofInverseImage Y f.hom.base).hom.c ≫
      (TopCat.Presheaf.pushforward CommRingCat.{u}
        (ofInverseImage Y f.hom.base).hom.base).map
        (toInverseImage f).hom.c ≍ f.hom.c
  rw [← inverseImageMap_unit_hom f]
  rfl

end AlgebraicGeometry.RingedSpace

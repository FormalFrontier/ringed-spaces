/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import RingedSpaces

/-!
# Aggregate-import clients for inverse-image module presheaves
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open RingedSpaces.Modules.PresheafInverseImage

namespace Test.PresheafInverseImageRoot

universe v

variable {X Y : TopCat.{v}} (f : X ⟶ Y) (R : Y.Presheaf RingCat.{v})
  (M : PresheafOfModules.{v} R)

theorem arbitraryScalarRestriction {U V : Opens X} (g : op U ⟶ op V)
    (r : ((Opens.map f).op.pointwiseLeftKanExtension R).obj (op U))
    (m : ((Opens.map f).op.pointwiseLeftKanExtension M.presheaf).obj (op U)) :
    letI := pointwiseModule f R M U
    letI := pointwiseModule f R M V
    (inverseImageModule f R M).map g (r • m) =
      ((Opens.map f).op.pointwiseLeftKanExtension R).map g r •
        (inverseImageModule f R M).map g m :=
  restriction_smul f R M g r m

theorem actualUnit (V : (Opens Y)ᵒᵖ) (r : R.obj V) (m : M.obj V) :
    pointwiseSmul f R M ((Opens.map f).obj (unop V))
        (((Opens.map f).op.pointwiseLeftKanExtensionUnit R).app V r)
        (((Opens.map f).op.pointwiseLeftKanExtensionUnit M.presheaf).app V m) =
      ((Opens.map f).op.pointwiseLeftKanExtensionUnit M.presheaf).app V (r • m) :=
  unit_smul f R M V r m

theorem fullUnderlyingIso :
    (underlyingComparison f R).hom.app M ≫ (underlyingComparison f R).inv.app M =
      𝟙 ((inverseImageFunctor f R ⋙
        PresheafOfModules.toPresheaf
          ((Opens.map f).op.pointwiseLeftKanExtension R)).obj M) := by
  exact congrArg (fun η => η.app M) (underlyingComparison f R).hom_inv_id

theorem additiveUnitComparison :
    (Opens.map f).op.pointwiseLeftKanExtensionUnit M.presheaf ≫
      (Opens.map f).op.whiskerLeft ((underlyingComparison f R).hom.app M) =
        (Opens.map f).op.leftKanExtensionUnit M.presheaf :=
  pointwiseToPullback_fac f M.presheaf

end Test.PresheafInverseImageRoot

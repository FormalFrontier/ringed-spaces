/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import RingedSpaces.Modules.RingedSpacePushforward

set_option warningAsError true

/-!
# Public client for pushforward through a full ringed-space morphism

The map is arbitrary: no base identity, local-ring assumption, nonzero ring or
nonempty-space hypothesis enters the comparison.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open RingedSpaces.Modules.RingedSpacePushforward

namespace Test.RingedSpacePushforward

universe u

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y)

theorem completeMap :
    RingedSpaces.Modules.SheafInverseImage.actualUnit f.hom.base Y.sheaf ≫
      (TopCat.Sheaf.pushforward RingCat.{u} f.hom.base).map (ringSheafMap f) =
    structureMap f :=
  actualUnit_comp_ringSheafMap f

theorem actualOpen (U : (Opens Y.carrier)ᵒᵖ) (r : Y.sheaf.obj.obj U) :
    (structureMap f).hom.app U r = f.hom.c.app U r :=
  structureMap_original f U r

/-- The native full-map comparison for arbitrary ringed spaces. -/
noncomputable def comparison :
    SheafOfModules.restrictScalars (ringSheafMap f) ⋙
      RingedSpaces.Modules.SheafInverseImage.pushforwardFunctor f.hom.base Y.sheaf ≅
    pushforwardFunctor f :=
  restrictPushforwardIso f

theorem forwardOpen (M : SheafOfModules.{u} (ringSheaf X))
    (U : (Opens Y.carrier)ᵒᵖ)
    (m : ((SheafOfModules.restrictScalars (ringSheafMap f) ⋙
      RingedSpaces.Modules.SheafInverseImage.pushforwardFunctor f.hom.base Y.sheaf).obj M).val.obj U) :
    ((comparison f).hom.app M).val.app U m = m :=
  restrictPushforwardIso_hom_app f M U m

theorem backwardOpen (M : SheafOfModules.{u} (ringSheaf X))
    (U : (Opens Y.carrier)ᵒᵖ) (m : ((pushforwardFunctor f).obj M).val.obj U) :
    ((comparison f).inv.app M).val.app U m = m :=
  restrictPushforwardIso_inv_app f M U m

theorem natural {M N : SheafOfModules.{u} (ringSheaf X)} (h : M ⟶ N) :
    (SheafOfModules.restrictScalars (ringSheafMap f) ⋙
      RingedSpaces.Modules.SheafInverseImage.pushforwardFunctor f.hom.base Y.sheaf).map h ≫
        (comparison f).hom.app N =
      (comparison f).hom.app M ≫ (pushforwardFunctor f).map h :=
  restrictPushforwardIso_naturality f h

end Test.RingedSpacePushforward

#lint

/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import RingedSpaces

set_option warningAsError true

/-!
# Root-only client for full ringed-space module morphisms

The sole import is the public aggregate. The full structure map, natural
pushforward comparison and explicit right-tensor pullback adjunction work for
an arbitrary morphism of ringed spaces in diagonal universes.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open RingedSpaces.Modules.RingedSpacePushforward
open RingedSpaces.Modules.RingedSpacePullback

namespace Test.RingedSpaceFullMorphismRoot

universe u

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y)

theorem originalStructureMap (U : (Opens Y.carrier)ᵒᵖ)
    (value : Y.sheaf.obj.obj U) :
    (structureMap f).hom.app U value = f.hom.c.app U value :=
  structureMap_original f U value

theorem fullMate :
    RingedSpaces.Modules.SheafInverseImage.actualUnit f.hom.base Y.sheaf ≫
      (TopCat.Sheaf.pushforward RingCat.{u} f.hom.base).map (ringSheafMap f) =
    structureMap f :=
  actualUnit_comp_ringSheafMap f

theorem pushforwardComparisonNatural
    {M N : SheafOfModules.{u} (ringSheaf X)} (map : M ⟶ N) :
    (SheafOfModules.restrictScalars (ringSheafMap f) ⋙
      RingedSpaces.Modules.SheafInverseImage.pushforwardFunctor f.hom.base Y.sheaf).map map ≫
        (restrictPushforwardIso f).hom.app N =
      (restrictPushforwardIso f).hom.app M ≫ (pushforwardFunctor f).map map :=
  restrictPushforwardIso_naturality f map

variable (M : SheafOfModules.{u} (ringSheaf Y))
variable (N : SheafOfModules.{u} (ringSheaf X))

/-- The right-tensor sheafified pullback is left adjoint to full pushforward. -/
noncomputable def fullAdjunction :
    pullbackFunctor f ⊣ pushforwardFunctor f :=
  adjunction f

theorem homEquivLeftInverse (map : (pullbackFunctor f).obj M ⟶ N) :
    (homEquiv f M N).symm (homEquiv f M N map) = map :=
  (homEquiv_inverse_laws f M N).1 map

theorem fullUnit :
    (adjunction f).unit.app M =
      homEquiv f M ((pullbackFunctor f).obj M) (𝟙 _) := by
  rfl

/-- The explicit pullback has the canonical adjunction-level native comparison. -/
noncomputable def nativePullbackComparison :
    pullbackFunctor f ≅ SheafOfModules.pullback (structureMap f) :=
  nativeComparison f

theorem nativeUnit :
    (adjunction f).unit.app M ≫
      (pushforwardFunctor f).map ((nativeComparison f).hom.app M) =
        (nativeAdjunction f).unit.app M :=
  nativeComparison_unit f M

end Test.RingedSpaceFullMorphismRoot

#lint

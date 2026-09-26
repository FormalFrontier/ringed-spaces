/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import RingedSpaces

/-!
# Root-only client for inverse-image sheaf modules

All results use only the aggregate public import, for an arbitrary continuous map.
-/

@[expose] public section

open CategoryTheory
open RingedSpaces.Modules.SheafInverseImage

namespace Test.SheafInverseImageRoot

universe v

variable {X Y : TopCat.{v}} (f : X ⟶ Y) (S : Y.Sheaf CommRingCat.{v})
  (M : SheafOfModules.{v} (sourceRing S))
  (N : SheafOfModules.{v} (targetRing f S))

theorem rootFunctorMaps (M' M'' : SheafOfModules.{v} (sourceRing S))
    (h : M ⟶ M') (h' : M' ⟶ M'') :
    (moduleFunctor f S).map (𝟙 M) = 𝟙 ((moduleFunctor f S).obj M) ∧
      (moduleFunctor f S).map (h ≫ h') =
        (moduleFunctor f S).map h ≫ (moduleFunctor f S).map h' :=
  ⟨(moduleFunctor f S).map_id M, (moduleFunctor f S).map_comp h h'⟩

theorem rootComparisonNatural {T : Y.Sheaf CommRingCat.{v}} (h : S ⟶ T) :
    (TopCat.Sheaf.pullback CommRingCat.{v} f ⋙ sheafForget X).map h ≫
      (comparisonNatIso f).hom.app T =
    (comparisonNatIso f).hom.app S ≫
      (sheafForget Y ⋙ TopCat.Sheaf.pullback RingCat.{v} f).map h :=
  (comparisonNatIso f).hom.naturality h

theorem rootWholeRingUnit :
    actualUnit f S ≫
      (TopCat.Sheaf.pushforward RingCat.{v} f).map (ringIso f S).hom =
      pointwiseSheafUnit f RingCat.{v} (sourceRing S) :=
  ringUnit_iso f S

theorem rootUnderlyingNatural
    (M' : SheafOfModules.{v} (sourceRing S)) (h : M ⟶ M') :
    (moduleFunctor f S ⋙ SheafOfModules.toSheaf (targetRing f S)).map h ≫
      (moduleUnderlyingNatIso f S).hom.app M' =
    (moduleUnderlyingNatIso f S).hom.app M ≫
      (SheafOfModules.toSheaf (sourceRing S) ⋙
        TopCat.Sheaf.pullback AddCommGrpCat.{v} f).map h :=
  (moduleUnderlyingNatIso f S).hom.naturality h

theorem rootBothDirections (g : (moduleFunctor f S).obj M ⟶ N)
    (h : M ⟶ (pushforwardFunctor f S).obj N) :
    backward f S (forward f S g) = g ∧ forward f S (backward f S h) = h :=
  ⟨backward_forward f S g, forward_backward f S h⟩

theorem rootSourceNaturality
    (M' : SheafOfModules.{v} (sourceRing S)) (h : M' ⟶ M)
    (g : (moduleFunctor f S).obj M ⟶ N) :
    homEquiv f S M' N ((moduleFunctor f S).map h ≫ g) =
      h ≫ homEquiv f S M N g :=
  homEquiv_naturality_left f S h g

theorem rootTargetNaturality
    (N' : SheafOfModules.{v} (targetRing f S))
    (h : N ⟶ N') (g : (moduleFunctor f S).obj M ⟶ N) :
    homEquiv f S M N' (g ≫ h) =
      homEquiv f S M N g ≫ (pushforwardFunctor f S).map h :=
  homEquiv_naturality_right f S g h

theorem rootWholeAdditiveUnit :
    (SheafOfModules.toSheaf (sourceRing S)).map ((adjunction f S).unit.app M) =
      moduleUnit f S M :=
  unit_underlying f S M

theorem rootBothTriangles :
    (moduleFunctor f S).map ((adjunction f S).unit.app M) ≫
      (adjunction f S).counit.app ((moduleFunctor f S).obj M) =
        𝟙 ((moduleFunctor f S).obj M) ∧
      (adjunction f S).unit.app ((pushforwardFunctor f S).obj N) ≫
      (pushforwardFunctor f S).map ((adjunction f S).counit.app N) =
        𝟙 ((pushforwardFunctor f S).obj N) :=
  ⟨left_triangle f S M, right_triangle f S N⟩

end Test.SheafInverseImageRoot

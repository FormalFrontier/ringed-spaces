/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import RingedSpaces.Modules.RingedSpacePullback

set_option warningAsError true

/-!
# Public-only arbitrary-full-morphism pullback client

Nothing below assumes a local map, a nonidentity base, a nonempty space or a
nonzero coefficient ring. All witnesses are imported from the new library leaf.
-/

@[expose] public section

open CategoryTheory
open RingedSpaces.Modules.RingedSpacePullback

namespace Test.RingedSpacePullback

universe u

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y)
variable (M : SheafOfModules.{u} (RingedSpaces.Modules.RingedSpacePushforward.ringSheaf Y))
variable (N : SheafOfModules.{u} (RingedSpaces.Modules.RingedSpacePushforward.ringSheaf X))

/-- The explicit right-tensor pullback and actual full pushforward are adjoints. -/
noncomputable def fullAdjunction :
    pullbackFunctor f ⊣ RingedSpaces.Modules.RingedSpacePushforward.pushforwardFunctor f :=
  adjunction f

theorem leftInverse (h : (pullbackFunctor f).obj M ⟶ N) :
    (homEquiv f M N).symm (homEquiv f M N h) = h :=
  (homEquiv_inverse_laws f M N).1 h

theorem rightInverse
    (k : M ⟶ (RingedSpaces.Modules.RingedSpacePushforward.pushforwardFunctor f).obj N) :
    homEquiv f M N ((homEquiv f M N).symm k) = k :=
  (homEquiv_inverse_laws f M N).2 k

theorem sourceNatural {M' : SheafOfModules.{u}
    (RingedSpaces.Modules.RingedSpacePushforward.ringSheaf Y)}
    (g : M' ⟶ M) (h : (pullbackFunctor f).obj M ⟶ N) :
    homEquiv f M' N ((pullbackFunctor f).map g ≫ h) = g ≫ homEquiv f M N h :=
  homEquiv_naturality_left f g N h

theorem targetNatural {N' : SheafOfModules.{u}
    (RingedSpaces.Modules.RingedSpacePushforward.ringSheaf X)}
    (h : (pullbackFunctor f).obj M ⟶ N) (g : N ⟶ N') :
    homEquiv f M N' (h ≫ g) =
      homEquiv f M N h ≫
        (RingedSpaces.Modules.RingedSpacePushforward.pushforwardFunctor f).map g :=
  homEquiv_naturality_right f M h g

theorem fullUnit :
    (adjunction f).unit.app M = homEquiv f M ((pullbackFunctor f).obj M) (𝟙 _) := by
  rfl

theorem nativeUnit :
    (adjunction f).unit.app M ≫
      (RingedSpaces.Modules.RingedSpacePushforward.pushforwardFunctor f).map
        ((nativeComparison f).hom.app M) = (nativeAdjunction f).unit.app M :=
  nativeComparison_unit f M

theorem nativeTransposes
    (h : (SheafOfModules.pullback
      (RingedSpaces.Modules.RingedSpacePushforward.structureMap f)).obj M ⟶ N) :
    homEquiv f M N ((nativeComparison f).hom.app M ≫ h) =
      (nativeAdjunction f).homEquiv M N h :=
  nativeComparison_homEquiv f M N h

theorem bothTriangles :
    (pullbackFunctor f).map ((adjunction f).unit.app M) ≫
        (adjunction f).counit.app ((pullbackFunctor f).obj M) = 𝟙 _ ∧
      (adjunction f).unit.app
          ((RingedSpaces.Modules.RingedSpacePushforward.pushforwardFunctor f).obj N) ≫
        (RingedSpaces.Modules.RingedSpacePushforward.pushforwardFunctor f).map
          ((adjunction f).counit.app N) = 𝟙 _ :=
  triangle_identities f M N

end Test.RingedSpacePullback

#lint

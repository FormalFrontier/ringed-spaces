/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import RingedSpaces.Modules.RingedSpacePullback
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous

/-!
# Composition and identity for module sheaves on ringed spaces

The functors below use full ringed-space morphisms. In particular, `L` is the
sheafified ordinary inverse image followed by extension of scalars from the
released ringed-spaces library, and `A` is its actual adjunction to `R`.
The canonical comparisons are natural isomorphisms, not equalities of functors.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
set_option warningAsError true

@[expose] public section

namespace RingedSpaces.Modules.PullbackCoherence

open CategoryTheory CategoryTheory.Functor TopologicalSpace

universe u

/-- The category of module sheaves over the structure sheaf. -/
abbrev ModuleSheaves (X : AlgebraicGeometry.RingedSpace.{u, u}) :=
  SheafOfModules.{u} (RingedSpacePushforward.ringSheaf X)

/-- Direct image along a full ringed-space morphism. -/
noncomputable abbrev R {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y) :=
  RingedSpacePushforward.pushforwardFunctor f

/-- Inverse image of module sheaves, including extension of scalars. -/
noncomputable abbrev L {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y) :=
  RingedSpacePullback.pullbackFunctor f

/-- The inverse-image/direct-image adjunction. -/
noncomputable abbrev A {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y) :=
  RingedSpacePullback.adjunction f

variable {X Y Z W : AlgebraicGeometry.RingedSpace.{u, u}}

/-- The inverse-image sites compose in the order of pullbacks. -/
theorem opensMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    Opens.map (f ≫ g).hom.base = Opens.map g.hom.base ⋙ Opens.map f.hom.base := rfl

/-- The coefficient map of the composite full morphism. -/
theorem structureMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    RingedSpacePushforward.structureMap (f ≫ g) =
      RingedSpacePushforward.structureMap g ≫
        (TopCat.Sheaf.pushforward RingCat.{u} g.hom.base).map
          (RingedSpacePushforward.structureMap f) := rfl

/-- Direct-image composition, including its coefficient change. -/
noncomputable def pushforwardComp (f : X ⟶ Y) (g : Y ⟶ Z) :
    R f ⋙ R g ≅ R (f ≫ g) :=
  SheafOfModules.pushforwardComp (RingedSpacePushforward.structureMap g)
    (RingedSpacePushforward.structureMap f)

/-- Direct image along the identity full morphism. -/
noncomputable def pushforwardId (X : AlgebraicGeometry.RingedSpace.{u, u}) :
    R (𝟙 X) ≅ 𝟭 (ModuleSheaves X) :=
  SheafOfModules.pushforwardId (RingedSpacePushforward.ringSheaf X)

/-- Inverse-image composition, transported across the actual adjunctions. -/
noncomputable def pullbackComp (f : X ⟶ Y) (g : Y ⟶ Z) :
    L g ⋙ L f ≅ L (f ≫ g) :=
  Adjunction.leftAdjointCompIso (A g) (A f) (A (f ≫ g)) (pushforwardComp f g)

/-- Inverse image along the identity full morphism. -/
noncomputable def pullbackId (X : AlgebraicGeometry.RingedSpace.{u, u}) :
    L (𝟙 X) ≅ 𝟭 (ModuleSheaves X) :=
  Adjunction.leftAdjointIdIso (A (𝟙 X)) (pushforwardId X)

/-- Naturality of the inverse-image composition comparison. -/
theorem pullbackComp_naturality (f : X ⟶ Y) (g : Y ⟶ Z)
    {M N : ModuleSheaves Z} (h : M ⟶ N) :
    (L g ⋙ L f).map h ≫ (pullbackComp f g).hom.app N =
      (pullbackComp f g).hom.app M ≫ (L (f ≫ g)).map h :=
  (pullbackComp f g).hom.naturality h

/-- The inverse of inverse-image composition is the mate of direct-image composition. -/
theorem pullbackComp_inverse_mate (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv ((A g).comp (A f)) (A (f ≫ g))
      (pullbackComp f g).inv = (pushforwardComp f g).hom :=
  Adjunction.conjugateEquiv_leftAdjointCompIso_inv
    (A g) (A f) (A (f ≫ g)) (pushforwardComp f g)

/-- The unit characterizes the inverse-image composition isomorphism. -/
theorem pullbackComp_unit (f : X ⟶ Y) (g : Y ⟶ Z) (M : ModuleSheaves Z) :
    ((A g).comp (A f)).unit.app M ≫
        (pushforwardComp f g).hom.app ((L g ⋙ L f).obj M) =
      (A (f ≫ g)).unit.app M ≫
        (R (f ≫ g)).map ((pullbackComp f g).inv.app M) := by
  rw [← pullbackComp_inverse_mate f g]
  exact unit_conjugateEquiv ((A g).comp (A f)) (A (f ≫ g))
    (pullbackComp f g).inv M

/-- The identity inverse-image isomorphism is the mate of the inverse identity direct image. -/
theorem pullbackId_mate (X : AlgebraicGeometry.RingedSpace.{u, u}) :
    conjugateEquiv .id (A (𝟙 X)) (pullbackId X).hom = (pushforwardId X).inv :=
  Adjunction.conjugateEquiv_leftAdjointIdIso_hom (A (𝟙 X)) (pushforwardId X)

/-- Right unit law for direct-image composition. -/
theorem pushforwardComp_rightUnit (f : X ⟶ Y) :
    pushforwardComp f (𝟙 Y) =
      isoWhiskerLeft (R f) (pushforwardId Y) ≪≫ rightUnitor (R f) := rfl

/-- Left unit law for direct-image composition. -/
theorem pushforwardComp_leftUnit (f : X ⟶ Y) :
    pushforwardComp (𝟙 X) f =
      isoWhiskerRight (pushforwardId X) (R f) ≪≫ leftUnitor (R f) := rfl

/-- Associativity of the three direct-image comparisons. -/
theorem pushforwardComp_assoc (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) :
    isoWhiskerLeft (R f) (pushforwardComp g h) ≪≫ pushforwardComp f (g ≫ h) =
      (associator (R f) (R g) (R h)).symm ≪≫
        isoWhiskerRight (pushforwardComp f g) (R h) ≪≫
          pushforwardComp (f ≫ g) h := rfl

/-- Right unit law for inverse-image composition. -/
theorem pullbackComp_rightUnit (f : X ⟶ Y) :
    pullbackComp f (𝟙 Y) =
      isoWhiskerRight (pullbackId Y) (L f) ≪≫ leftUnitor (L f) :=
  Adjunction.leftAdjointCompIso_id_comp (A (𝟙 Y)) (A f)
    (pushforwardComp f (𝟙 Y)) (pushforwardId Y) (pushforwardComp_rightUnit f)

/-- Left unit law for inverse-image composition. -/
theorem pullbackComp_leftUnit (f : X ⟶ Y) :
    pullbackComp (𝟙 X) f =
      isoWhiskerLeft (L f) (pullbackId X) ≪≫ rightUnitor (L f) :=
  Adjunction.leftAdjointCompIso_comp_id (A f) (A (𝟙 X))
    (pushforwardComp (𝟙 X) f) (pushforwardId X) (pushforwardComp_leftUnit f)

/-- Associativity of the three inverse-image comparisons. -/
theorem pullbackComp_assoc (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) :
    isoWhiskerLeft (L h) (pullbackComp f g) ≪≫ pullbackComp (f ≫ g) h =
      (associator (L h) (L g) (L f)).symm ≪≫
        isoWhiskerRight (pullbackComp g h) (L f) ≪≫ pullbackComp f (g ≫ h) :=
  Adjunction.leftAdjointCompIso_assoc (A h) (A g) (A f)
    (A (g ≫ h)) (A (f ≫ g)) (A (f ≫ g ≫ h))
    (pushforwardComp g h) (pushforwardComp f g)
    (pushforwardComp (f ≫ g) h) (pushforwardComp f (g ≫ h))
    (pushforwardComp_assoc f g h)

end RingedSpaces.Modules.PullbackCoherence

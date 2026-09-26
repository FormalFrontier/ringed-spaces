/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents, formalization-worker-a (non-Cartesian source fixture, Hive Task hive-request-d2ec8864379e910d5a7d9997da5e9b0dc357f7a8,
  UID 98fc3c95-98fd-4be6-b8b7-45e415272181),
  formalization-worker-b (Hive Task hive-request-9b96dab56bf41ce7554f74026cc8603719e3384c,
  UID 8d01f604-2c37-4eee-ba00-733cf8b4f2d4),
  formalization-worker-b (destination preparation, Hive Task hive-request-9ba8c100c88f6cb8d75c1f208a34c55974589c18,
  UID c17170b6-00a3-498c-9c19-d86aa575e29a)
-/
module

public import RingedSpaces
public import Mathlib.Data.ZMod.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Clients for module pullback coherence and square mates -/

set_option warningAsError true

@[expose] public section

namespace Test.RingedSpaceBaseChange

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open RingedSpaces.Modules.PullbackCoherence RingedSpaces.Modules.BaseChange

universe u

variable {W X Y Z T : RingedSpace.{u, u}}

/-- Coherence and the square mate are available for arbitrary full morphisms. -/
noncomputable example (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    L h ⋙ L g ⋙ L f ≅ L (f ≫ g ≫ h) :=
  isoWhiskerRight (pullbackComp g h) (L f) ≪≫ pullbackComp f (g ≫ h)

example (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    isoWhiskerLeft (L h) (pullbackComp f g) ≪≫ pullbackComp (f ≫ g) h =
      (associator (L h) (L g) (L f)).symm ≪≫
        isoWhiskerRight (pullbackComp g h) (L f) ≪≫ pullbackComp f (g ≫ h) :=
  pullbackComp_assoc f g h

example (top : X ⟶ Z) :
    pushPull (𝟙 X) top top (𝟙 Z) (by simp) ≫ (targetIdentity top).hom =
      (sourceIdentity top).hom :=
  pushPull_identity_normalized top

noncomputable example (bottom : W ⟶ X) (left : W ⟶ Y) (top : X ⟶ Z) (right : Y ⟶ Z)
    (commutes : bottom ≫ top = left ≫ right) (M : ModuleSheaves X) :
    (L right).obj ((R top).obj M) ⟶ (R left).obj ((L bottom).obj M) :=
  (pushPull bottom left top right commutes).app M

private local instance : TopologicalSpace PEmpty := ⊥
private local instance : TopologicalSpace PUnit := ⊥

def pointSpace : TopCat := TopCat.of PUnit

def emptySpace : TopCat := TopCat.of PEmpty

noncomputable def pointSheaf : pointSpace.Sheaf CommRingCat :=
  (presheafToSheaf (Opens.grothendieckTopology pointSpace) CommRingCat).obj
    ((Functor.const _).obj (CommRingCat.of (ZMod 1)))

noncomputable def pointRinged : RingedSpace.{0, 0} where
  carrier := pointSpace
  presheaf := pointSheaf.obj
  IsSheaf := pointSheaf.property

def fromEmpty : emptySpace ⟶ pointSpace := TopCat.const PUnit.unit

noncomputable def emptyCorner : RingedSpace.{0, 0} :=
  RingedSpace.inverseImage pointRinged fromEmpty

noncomputable def cornerMap : emptyCorner ⟶ pointRinged :=
  RingedSpace.ofInverseImage pointRinged fromEmpty

/-- The mate exists for an empty-corner square that is not Cartesian. -/
noncomputable def nonCartesianComparison :
    R (𝟙 pointRinged) ⋙ L (𝟙 pointRinged) ⟶ L cornerMap ⋙ R cornerMap :=
  pushPull cornerMap cornerMap (𝟙 pointRinged) (𝟙 pointRinged) (by simp)

theorem square_notCartesian :
    ¬ IsPullback cornerMap cornerMap (𝟙 pointRinged) (𝟙 pointRinged) := by
  intro square
  let impossible : PEmpty := by
    letI : IsIso cornerMap := square.isIso_fst_of_isIso
    exact (inv cornerMap).hom.base PUnit.unit
  exact PEmpty.elim impossible

end Test.RingedSpaceBaseChange

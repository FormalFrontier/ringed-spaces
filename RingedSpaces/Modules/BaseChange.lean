/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents, formalization-worker-a (source prototype, Hive Task hive-request-d2ec8864379e910d5a7d9997da5e9b0dc357f7a8,
  UID 98fc3c95-98fd-4be6-b8b7-45e415272181),
  formalization-worker-b (Hive Task hive-request-9b96dab56bf41ce7554f74026cc8603719e3384c,
  UID 8d01f604-2c37-4eee-ba00-733cf8b4f2d4),
  formalization-worker-b (destination preparation, Hive Task hive-request-9ba8c100c88f6cb8d75c1f208a34c55974589c18,
  UID c17170b6-00a3-498c-9c19-d86aa575e29a)
-/
module

public import RingedSpaces.Modules.PullbackCoherence
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Push–pull comparison for a commutative square of ringed spaces

For any full commutative square, this module constructs the actual mate of
direct-image composition. No Cartesian, flatness, or invertibility hypothesis
is imposed on the square or on the comparison.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

@[expose] public section

namespace RingedSpaces.Modules.BaseChange

open CategoryTheory CategoryTheory.Functor TopologicalSpace PullbackCoherence

universe u

variable {W X Y Z : AlgebraicGeometry.RingedSpace.{u, u}}

/-- The canonical comparison of direct images around a full commutative square. -/
noncomputable def pushforwardSquare (bottom : W ⟶ X) (left : W ⟶ Y)
    (top : X ⟶ Z) (right : Y ⟶ Z) (commutes : bottom ≫ top = left ≫ right) :
    R bottom ⋙ R top ≅ R left ⋙ R right :=
  pushforwardComp bottom top ≪≫ eqToIso (congrArg R commutes) ≪≫
    (pushforwardComp left right).symm

/-- The square's push–pull transformation is the mate of its direct-image comparison. -/
noncomputable def pushPull (bottom : W ⟶ X) (left : W ⟶ Y)
    (top : X ⟶ Z) (right : Y ⟶ Z) (commutes : bottom ≫ top = left ≫ right) :
    R top ⋙ L right ⟶ L bottom ⋙ R left :=
  (mateEquiv (A bottom) (A right)).symm
    (pushforwardSquare bottom left top right commutes).hom

/-- The transpose of each component of the push–pull mate. -/
theorem pushPull_transpose (bottom : W ⟶ X) (left : W ⟶ Y)
    (top : X ⟶ Z) (right : Y ⟶ Z) (commutes : bottom ≫ top = left ≫ right)
    (M : ModuleSheaves X) :
    (A right).homEquiv ((R top).obj M) ((R left).obj ((L bottom).obj M))
      ((pushPull bottom left top right commutes).app M) =
        (R top).map ((A bottom).unit.app M) ≫
          (pushforwardSquare bottom left top right commutes).hom.app ((L bottom).obj M) := by
  exact (unit_mateEquiv_symm (A bottom) (A right)
    (pushforwardSquare bottom left top right commutes).hom M).symm

/-- The unit identity that uniquely determines each push–pull component. -/
theorem pushPull_unit (bottom : W ⟶ X) (left : W ⟶ Y)
    (top : X ⟶ Z) (right : Y ⟶ Z) (commutes : bottom ≫ top = left ≫ right)
    (M : ModuleSheaves X) :
    (A right).unit.app ((R top).obj M) ≫
        (R right).map ((pushPull bottom left top right commutes).app M) =
      (R top).map ((A bottom).unit.app M) ≫
        (pushforwardSquare bottom left top right commutes).hom.app ((L bottom).obj M) := by
  simpa only [Adjunction.homEquiv_unit] using
    pushPull_transpose bottom left top right commutes M

/-- Uniqueness of the square mate by its unit identity. -/
theorem pushPull_unique (bottom : W ⟶ X) (left : W ⟶ Y)
    (top : X ⟶ Z) (right : Y ⟶ Z) (commutes : bottom ≫ top = left ≫ right)
    (M : ModuleSheaves X) (comparison : (L right).obj ((R top).obj M) ⟶
      (R left).obj ((L bottom).obj M))
    (unit_identity : (A right).unit.app ((R top).obj M) ≫ (R right).map comparison =
      (R top).map ((A bottom).unit.app M) ≫
        (pushforwardSquare bottom left top right commutes).hom.app ((L bottom).obj M)) :
    comparison = (pushPull bottom left top right commutes).app M := by
  apply ((A right).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, pushPull_transpose]
  exact unit_identity

/-- Naturality in the module sheaf. -/
theorem pushPull_naturality (bottom : W ⟶ X) (left : W ⟶ Y)
    (top : X ⟶ Z) (right : Y ⟶ Z) (commutes : bottom ≫ top = left ≫ right)
    {M N : ModuleSheaves X} (map : M ⟶ N) :
    (R top ⋙ L right).map map ≫ (pushPull bottom left top right commutes).app N =
      (pushPull bottom left top right commutes).app M ≫ (L bottom ⋙ R left).map map :=
  (pushPull bottom left top right commutes).naturality map

/-- Scalar linearity of the component on each open set follows from its bundled module map. -/
theorem pushPull_section_smul (bottom : W ⟶ X) (left : W ⟶ Y)
    (top : X ⟶ Z) (right : Y ⟶ Z) (commutes : bottom ≫ top = left ≫ right)
    (M : ModuleSheaves X) (U : Opens Y.carrier)
    (scalar : (RingedSpacePushforward.ringSheaf Y).obj.obj (.op U))
    (element : ((R top ⋙ L right).obj M).val.obj (.op U)) :
    (((pushPull bottom left top right commutes).app M).val.app (.op U)).hom
        (scalar • element) =
      scalar • (((pushPull bottom left top right commutes).app M).val.app (.op U)).hom
        element :=
  (((SheafOfModules.evaluation (RingedSpacePushforward.ringSheaf Y) (.op U)).map
    ((pushPull bottom left top right commutes).app M)).hom.map_smul scalar element)

/-- Compatibility with restriction maps follows from the bundled presheaf morphism. -/
theorem pushPull_restrict (bottom : W ⟶ X) (left : W ⟶ Y)
    (top : X ⟶ Z) (right : Y ⟶ Z) (commutes : bottom ≫ top = left ≫ right)
    (M : ModuleSheaves X) {U V : Opens Y.carrier} (inclusion : U ⟶ V)
    (element : ((R top ⋙ L right).obj M).val.obj (.op V)) :
    (((pushPull bottom left top right commutes).app M).val.app (.op U))
      (((R top ⋙ L right).obj M).val.map inclusion.op element) =
      (((L bottom ⋙ R left).obj M).val.map inclusion.op)
        (((pushPull bottom left top right commutes).app M).val.app (.op V) element) :=
  PresheafOfModules.naturality_apply
    (M₁ := ((R top ⋙ L right).obj M).val)
    (M₂ := ((L bottom ⋙ R left).obj M).val)
    ((pushPull bottom left top right commutes).app M).val inclusion.op element

/-- Canonical normalization of the source of the identity-vertical square mate. -/
noncomputable def sourceIdentity (top : X ⟶ Z) :
    R top ⋙ L (𝟙 Z) ≅ R top :=
  isoWhiskerLeft (R top) (pullbackId Z) ≪≫ CategoryTheory.Functor.rightUnitor (R top)

/-- Canonical normalization of the target of the identity-vertical square mate. -/
noncomputable def targetIdentity (top : X ⟶ Z) :
    L (𝟙 X) ⋙ R top ≅ R top :=
  isoWhiskerRight (pullbackId X) (R top) ≪≫ CategoryTheory.Functor.leftUnitor (R top)

/-- The direct-image comparison of an identity-vertical square. -/
theorem pushforwardSquare_identity (top : X ⟶ Z) :
    pushforwardSquare (𝟙 X) top top (𝟙 Z) (by simp) =
      isoWhiskerRight (pushforwardId X) (R top) ≪≫
        CategoryTheory.Functor.leftUnitor (R top) ≪≫
      (isoWhiskerLeft (R top) (pushforwardId Z) ≪≫
        CategoryTheory.Functor.rightUnitor (R top)).symm := by
  simp [pushforwardSquare, pushforwardComp_leftUnit, pushforwardComp_rightUnit]

/-- After direct-image identity normalization, the square comparison is the identity
on the remaining direct-image functor. -/
theorem pushforwardSquare_identity_app (top : X ⟶ Z) (M : ModuleSheaves X) :
    (pushforwardSquare (𝟙 X) top top (𝟙 Z) (by simp)).hom.app M ≫
      (pushforwardId Z).hom.app ((R top).obj M) =
        (R top).map ((pushforwardId X).hom.app M) := by
  rw [pushforwardSquare_identity]
  simp

/-- The inverse identity pullback comparison is the adjunction unit followed
by the direct-image identity comparison. -/
theorem pullbackId_unit (X : AlgebraicGeometry.RingedSpace.{u, u})
    (M : ModuleSheaves X) :
    (A (𝟙 X)).unit.app M ≫
      (pushforwardId X).hom.app ((L (𝟙 X)).obj M) =
        (pullbackId X).inv.app M := by
  exact (Adjunction.leftAdjointIdIso_inv_app (A (𝟙 X)) (pushforwardId X) M).symm

/-- The identity-square mate carries the inverse identity pullback comparison
across any full ringed-space morphism. -/
theorem pushPull_identity_inverse (top : X ⟶ Z) (M : ModuleSheaves X) :
    (pullbackId Z).inv.app ((R top).obj M) ≫
      (pushPull (𝟙 X) top top (𝟙 Z) (by simp)).app M =
        (R top).map ((pullbackId X).inv.app M) := by
  rw [← pullbackId_unit Z ((R top).obj M), ← pullbackId_unit X M]
  simp only [Category.assoc]
  have hz := (pushforwardId Z).hom.naturality
    ((pushPull (𝟙 X) top top (𝟙 Z) (by simp)).app M)
  simp only [Functor.id_map, Functor.comp_obj] at hz
  rw [← hz]
  rw [← Category.assoc, pushPull_unit]
  rw [Category.assoc, pushforwardSquare_identity_app top ((L (𝟙 X)).obj M)]
  rw [← Functor.map_comp, pullbackId_unit X M]

/-- For the square with identity vertical arrows, the actual push–pull mate
normalizes to the identity on direct image via the *oriented* pullback-identity
isomorphisms `sourceIdentity` and `targetIdentity`. -/
theorem pushPull_identity_normalized (top : X ⟶ Z) :
    pushPull (𝟙 X) top top (𝟙 Z) (by simp) ≫ (targetIdentity top).hom =
      (sourceIdentity top).hom := by
  apply NatTrans.ext
  funext M
  change (pushPull (𝟙 X) top top (𝟙 Z) (by simp)).app M ≫
      (R top).map ((pullbackId X).hom.app M) =
    (pullbackId Z).hom.app ((R top).obj M)
  have key := pushPull_identity_inverse top M
  calc
    _ = ((pullbackId Z).hom.app ((R top).obj M) ≫
        (pullbackId Z).inv.app ((R top).obj M)) ≫
        ((pushPull (𝟙 X) top top (𝟙 Z) (by simp)).app M ≫
          (R top).map ((pullbackId X).hom.app M)) := by simp
    _ = (pullbackId Z).hom.app ((R top).obj M) ≫
          ((pullbackId Z).inv.app ((R top).obj M) ≫
            (pushPull (𝟙 X) top top (𝟙 Z) (by simp)).app M) ≫
          (R top).map ((pullbackId X).hom.app M) := by simp [Category.assoc]
    _ = (pullbackId Z).hom.app ((R top).obj M) ≫
          (R top).map ((pullbackId X).inv.app M) ≫
          (R top).map ((pullbackId X).hom.app M) := by rw [key]
    _ = _ := by simp [← Functor.map_comp]

end RingedSpaces.Modules.BaseChange

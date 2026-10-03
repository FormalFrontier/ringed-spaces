/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import RingedSpaces.Modules.PresheafInverseImageHom

/-!
# Direct clients for the concrete inverse-image Hom equivalence

These statements use the actual pointwise Kan ring, the accepted module action,
and mathlib's native module pushforward. The source and target are arbitrary.
-/

@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace
open RingedSpaces.Modules.PresheafInverseImage

namespace Test.PresheafInverseImageHom

universe v

variable {X Y : TopCat.{v}} (f : X ⟶ Y) (R : Y.Presheaf RingCat.{v})
  (M : PresheafOfModules.{v} R)
  (N : PresheafOfModules.{v} ((Opens.map f).op.pointwiseLeftKanExtension R))

theorem forwardSection
    (g : (inverseImageFunctor f R).obj M ⟶ N)
    (V : (Opens Y)ᵒᵖ) (m : M.obj V) :
    (forward f R g).app V m =
      g.app ((Opens.map f).op.obj V)
        (((Opens.map f).op.pointwiseLeftKanExtensionUnit M.presheaf).app V m) :=
  forward_apply f R g V m

theorem descentGenerator
    (h : M ⟶ (PresheafOfModules.pushforward (F := Opens.map f)
      ((Opens.map f).op.pointwiseLeftKanExtensionUnit R)).obj N)
    (U : Opens X) (i : index f U) (m : M.obj i.left) :
    (backward f R h).app (op U)
      ((colimit.ι (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ M.presheaf) i) m) =
        N.map i.hom (h.app i.left m) :=
  backward_ι f R h U i m

theorem descentArbitraryScalar
    (h : M ⟶ (PresheafOfModules.pushforward (F := Opens.map f)
      ((Opens.map f).op.pointwiseLeftKanExtensionUnit R)).obj N)
    (U : (Opens X)ᵒᵖ)
    (r : ((Opens.map f).op.pointwiseLeftKanExtension R).obj U)
    (m : (inverseImageFunctor f R |>.obj M).obj U) :
    (backward f R h).app U (r • m) = r • (backward f R h).app U m :=
  backward_smul f R h U r m

theorem bothHomDirections
    (g : (inverseImageFunctor f R).obj M ⟶ N)
    (h : M ⟶ (PresheafOfModules.pushforward (F := Opens.map f)
      ((Opens.map f).op.pointwiseLeftKanExtensionUnit R)).obj N) :
    (homEquiv f R M N).symm ((homEquiv f R M N) g) = g ∧
      (homEquiv f R M N) ((homEquiv f R M N).symm h) = h :=
  ⟨(homEquiv f R M N).left_inv g, (homEquiv f R M N).right_inv h⟩

theorem sourceNaturality {M' : PresheafOfModules.{v} R}
    (φ : M' ⟶ M) (g : (inverseImageFunctor f R).obj M ⟶ N)
    (h : M ⟶ (PresheafOfModules.pushforward (F := Opens.map f)
      ((Opens.map f).op.pointwiseLeftKanExtensionUnit R)).obj N) :
    forward f R ((inverseImageFunctor f R).map φ ≫ g) = φ ≫ forward f R g ∧
      backward f R (φ ≫ h) = (inverseImageFunctor f R).map φ ≫ backward f R h :=
  ⟨forward_naturality_left f R φ g, backward_naturality_left f R φ h⟩

theorem targetNaturality
    {N' : PresheafOfModules.{v} ((Opens.map f).op.pointwiseLeftKanExtension R)}
    (ψ : N ⟶ N') (g : (inverseImageFunctor f R).obj M ⟶ N)
    (h : M ⟶ (PresheafOfModules.pushforward (F := Opens.map f)
      ((Opens.map f).op.pointwiseLeftKanExtensionUnit R)).obj N) :
    forward f R (g ≫ ψ) =
        forward f R g ≫ (PresheafOfModules.pushforward (F := Opens.map f)
          ((Opens.map f).op.pointwiseLeftKanExtensionUnit R)).map ψ ∧
      backward f R (h ≫ (PresheafOfModules.pushforward (F := Opens.map f)
          ((Opens.map f).op.pointwiseLeftKanExtensionUnit R)).map ψ) =
        backward f R h ≫ ψ :=
  ⟨forward_naturality_right f R g ψ, backward_naturality_right f R h ψ⟩

theorem actualUnitSection (V : (Opens Y)ᵒᵖ) (m : M.obj V) :
    ((adjunction f R).unit.app M).app V m =
      ((Opens.map f).op.pointwiseLeftKanExtensionUnit M.presheaf).app V m :=
  unit_apply f R M V m

theorem actualCounitGenerator (U : Opens X) (i : index f U)
    (m : ((PresheafOfModules.pushforward (F := Opens.map f)
      ((Opens.map f).op.pointwiseLeftKanExtensionUnit R)).obj N).obj i.left) :
    ((adjunction f R).counit.app N).app (op U)
      ((colimit.ι (CostructuredArrow.proj (Opens.map f).op (op U) ⋙
        ((PresheafOfModules.pushforward (F := Opens.map f)
          ((Opens.map f).op.pointwiseLeftKanExtensionUnit R)).obj N).presheaf) i) m) =
      N.map i.hom m :=
  counit_ι f R N U i m

theorem actualUnitCounitNaturalities
    {M' : PresheafOfModules.{v} R}
    {N' : PresheafOfModules.{v} ((Opens.map f).op.pointwiseLeftKanExtension R)}
    (φ : M ⟶ M') (ψ : N ⟶ N') :
    φ ≫ (adjunction f R).unit.app M' =
        (adjunction f R).unit.app M ≫
          ((inverseImageFunctor f R) ⋙
            (PresheafOfModules.pushforward (F := Opens.map f)
              ((Opens.map f).op.pointwiseLeftKanExtensionUnit R))).map φ ∧
      ((PresheafOfModules.pushforward (F := Opens.map f)
        ((Opens.map f).op.pointwiseLeftKanExtensionUnit R)) ⋙
        inverseImageFunctor f R).map ψ ≫ (adjunction f R).counit.app N' =
      (adjunction f R).counit.app N ≫ ψ :=
  ⟨unit_naturality f R φ, counit_naturality f R ψ⟩

theorem bothTriangleIdentities :
    (inverseImageFunctor f R).map ((adjunction f R).unit.app M) ≫
        (adjunction f R).counit.app ((inverseImageFunctor f R).obj M) =
        𝟙 _ ∧
      (adjunction f R).unit.app ((PresheafOfModules.pushforward (F := Opens.map f)
          ((Opens.map f).op.pointwiseLeftKanExtensionUnit R)).obj N) ≫
        (PresheafOfModules.pushforward (F := Opens.map f)
          ((Opens.map f).op.pointwiseLeftKanExtensionUnit R)).map
            ((adjunction f R).counit.app N) = 𝟙 _ := by
  constructor
  · exact (adjunction f R).left_triangle_components _
  · exact (adjunction f R).right_triangle_components _

theorem ordinaryAdditiveTranspose
    (g : (inverseImageFunctor f R).obj M ⟶ N) :
    (PresheafOfModules.toPresheaf R).map (forward f R g) ≫
      ((PresheafOfModules.pushforwardCompToPresheaf (F := Opens.map f)
        ((Opens.map f).op.pointwiseLeftKanExtensionUnit R)).app N).hom =
    (TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{v} f).homEquiv
      M.presheaf N.presheaf
      ((underlyingComparison f R).inv.app M ≫
        (PresheafOfModules.toPresheaf _).map g) :=
  forward_underlying_additive f R g

end Test.PresheafInverseImageHom

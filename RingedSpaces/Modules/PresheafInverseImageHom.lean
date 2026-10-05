/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import RingedSpaces.Modules.PresheafInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Hom adjunction for inverse-image module presheaves

For a continuous map of spaces, the ordinary inverse-image module-presheaf
functor is left adjoint to the corresponding pushforward of modules. The
forward and backward natural transformations identify the actual action on
sections and expose the unit, counit and natural Hom equivalence.

## References

* Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry* (21 October 2025
  draft), §2.7.2 (p. 93) and Exercise 7.2.D(b,e) (p. 205): motivation for the
  inverse-image presheaf prerequisite to full module pullback. The bundled
  linear Hom adjunction for `RingCat` presheaves, including noncommutative
  coefficients, is a project proof, not an asserted sheaf-level result here.
-/

@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace

namespace RingedSpaces.Modules.PresheafInverseImage

universe v

variable {X Y : TopCat.{v}} (f : X ⟶ Y) (R : Y.Presheaf RingCat.{v})

/-- The underlying ordinary additive Kan-unit map of a module morphism. -/
private noncomputable def forwardUnderlying {M : PresheafOfModules.{v} R}
    {N : PresheafOfModules.{v} ((Opens.map f).op.pointwiseLeftKanExtension R)}
    (g : (inverseImageFunctor f R).obj M ⟶ N) :
    M.presheaf ⟶ ((PresheafOfModules.pushforward (F := Opens.map f)
      ((Opens.map f).op.pointwiseLeftKanExtensionUnit R)).obj N).presheaf :=
  (Opens.map f).op.pointwiseLeftKanExtensionUnit M.presheaf ≫
    (Opens.map f).op.whiskerLeft
      ((PresheafOfModules.toPresheaf
        ((Opens.map f).op.pointwiseLeftKanExtension R)).map g) ≫
    ((PresheafOfModules.pushforwardCompToPresheaf (F := Opens.map f)
      ((Opens.map f).op.pointwiseLeftKanExtensionUnit R)).app N).inv

/-- The underlying Kan descent of a module morphism into the genuine pushforward. -/
private noncomputable def backwardUnderlying {M : PresheafOfModules.{v} R}
    {N : PresheafOfModules.{v} ((Opens.map f).op.pointwiseLeftKanExtension R)}
    (h : M ⟶ (PresheafOfModules.pushforward (F := Opens.map f)
      ((Opens.map f).op.pointwiseLeftKanExtensionUnit R)).obj N) :
    (Opens.map f).op.pointwiseLeftKanExtension M.presheaf ⟶ N.presheaf :=
  ((Opens.map f).op.pointwiseLeftKanExtension M.presheaf).descOfIsLeftKanExtension
    ((Opens.map f).op.pointwiseLeftKanExtensionUnit M.presheaf) N.presheaf
    ((PresheafOfModules.toPresheaf R).map h ≫
      ((PresheafOfModules.pushforwardCompToPresheaf (F := Opens.map f)
        ((Opens.map f).op.pointwiseLeftKanExtensionUnit R)).app N).hom)

private theorem backwardUnderlying_ι {M : PresheafOfModules.{v} R}
    {N : PresheafOfModules.{v} ((Opens.map f).op.pointwiseLeftKanExtension R)}
    (h : M ⟶ (PresheafOfModules.pushforward (F := Opens.map f)
      ((Opens.map f).op.pointwiseLeftKanExtensionUnit R)).obj N)
    (U : Opens X) (i : index f U) (m : M.obj i.left) :
    (backwardUnderlying f R h).app (op U)
        ((colimit.ι (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ M.presheaf) i) m) =
      N.map i.hom (h.app i.left m) := by
  simp only [backwardUnderlying, Functor.pointwiseLeftKanExtension_desc_app]
  change (colimit.ι (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ M.presheaf) i ≫
      colimit.desc _ (Functor.costructuredArrowMapCocone (Opens.map f).op M.presheaf N.presheaf
        ((PresheafOfModules.toPresheaf R).map h ≫
          ((PresheafOfModules.pushforwardCompToPresheaf (F := Opens.map f)
            ((Opens.map f).op.pointwiseLeftKanExtensionUnit R)).app N).hom)
        (op U))).hom m = _
  rw [colimit.ι_desc]
  rfl

private theorem ring_ι_eq_map_unit (U : Opens X)
    (i : index f U) (r : R.obj i.left) :
    (colimit.ι (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ R) i) r =
      ((Opens.map f).op.pointwiseLeftKanExtension R).map i.hom
        (((Opens.map f).op.pointwiseLeftKanExtensionUnit R).app i.left r) := by
  let j : index f ((Opens.map f).obj (unop i.left)) :=
    CostructuredArrow.mk (𝟙 ((Opens.map f).op.obj i.left))
  change _ = ((Opens.map f).op.pointwiseLeftKanExtension R).map i.hom
    ((colimit.ι (CostructuredArrow.proj (Opens.map f).op
      ((Opens.map f).op.obj i.left) ⋙ R) j) r)
  erw [ring_map_ι f R i.hom j r]
  congr 1

private theorem backwardUnderlying_smul {M : PresheafOfModules.{v} R}
    {N : PresheafOfModules.{v} ((Opens.map f).op.pointwiseLeftKanExtension R)}
    (h : M ⟶ (PresheafOfModules.pushforward (F := Opens.map f)
      ((Opens.map f).op.pointwiseLeftKanExtensionUnit R)).obj N)
    (U : (Opens X)ᵒᵖ)
    (r : ((Opens.map f).op.pointwiseLeftKanExtension R).obj U)
    (m : (inverseImageFunctor f R |>.obj M).obj U) :
    (backwardUnderlying f R h).app U (r • m) =
      r • (backwardUnderlying f R h).app U m := by
  obtain ⟨i, a, b, ha, hb⟩ :=
    pointwise_jointly_surjective f R M (unop U) r m
  subst r
  subst m
  erw [← pointwise_smul_ι f R M (unop U) i a b]
  erw [backwardUnderlying_ι f R h (unop U) i (a • b),
    backwardUnderlying_ι f R h (unop U) i b]
  erw [ring_ι_eq_map_unit f R (unop U) i a]
  change N.map i.hom (h.app i.left (a • b)) =
    (((Opens.map f).op.pointwiseLeftKanExtension R).map i.hom
      (((Opens.map f).op.pointwiseLeftKanExtensionUnit R).app i.left a)) •
      N.map i.hom (h.app i.left b)
  rw [map_smul]
  exact N.map_smul i.hom
    (((Opens.map f).op.pointwiseLeftKanExtensionUnit R).app i.left a)
    (h.app i.left b)

private theorem forwardUnderlying_apply {M : PresheafOfModules.{v} R}
    {N : PresheafOfModules.{v} ((Opens.map f).op.pointwiseLeftKanExtension R)}
    (g : (inverseImageFunctor f R).obj M ⟶ N)
    (V : (Opens Y)ᵒᵖ) (m : M.obj V) :
    (forwardUnderlying f R g).app V m =
      g.app ((Opens.map f).op.obj V)
        (((Opens.map f).op.pointwiseLeftKanExtensionUnit M.presheaf).app V m) := rfl

private theorem forwardUnderlying_smul {M : PresheafOfModules.{v} R}
    {N : PresheafOfModules.{v} ((Opens.map f).op.pointwiseLeftKanExtension R)}
    (g : (inverseImageFunctor f R).obj M ⟶ N)
    (V : (Opens Y)ᵒᵖ) (r : R.obj V) (m : M.obj V) :
    (forwardUnderlying f R g).app V (r • m) =
      r • (forwardUnderlying f R g).app V m := by
  rw [forwardUnderlying_apply f R g V (r • m), forwardUnderlying_apply f R g V m]
  change g.app ((Opens.map f).op.obj V)
      (((Opens.map f).op.pointwiseLeftKanExtensionUnit M.presheaf).app V (r • m)) =
    (((Opens.map f).op.pointwiseLeftKanExtensionUnit R).app V r) •
      g.app ((Opens.map f).op.obj V)
        (((Opens.map f).op.pointwiseLeftKanExtensionUnit M.presheaf).app V m)
  rw [← unit_smul f R M V r m]
  exact (g.app ((Opens.map f).op.obj V)).hom.map_smul _ _

/-- The actual additive Kan-unit map, shown linear over the source ring. -/
noncomputable def forward {M : PresheafOfModules.{v} R}
    {N : PresheafOfModules.{v} ((Opens.map f).op.pointwiseLeftKanExtension R)}
    (g : (inverseImageFunctor f R).obj M ⟶ N) :
    M ⟶ (PresheafOfModules.pushforward (F := Opens.map f)
      ((Opens.map f).op.pointwiseLeftKanExtensionUnit R)).obj N :=
  PresheafOfModules.homMk
    ((Opens.map f).op.pointwiseLeftKanExtensionUnit M.presheaf ≫
      (Opens.map f).op.whiskerLeft
        ((PresheafOfModules.toPresheaf
          ((Opens.map f).op.pointwiseLeftKanExtension R)).map g) ≫
      ((PresheafOfModules.pushforwardCompToPresheaf (F := Opens.map f)
        ((Opens.map f).op.pointwiseLeftKanExtensionUnit R)).app N).inv)
    (by
      intro V r m
      change g.app ((Opens.map f).op.obj V)
          (((Opens.map f).op.pointwiseLeftKanExtensionUnit M.presheaf).app V (r • m)) =
        (((Opens.map f).op.pointwiseLeftKanExtensionUnit R).app V r) •
          g.app ((Opens.map f).op.obj V)
            (((Opens.map f).op.pointwiseLeftKanExtensionUnit M.presheaf).app V m)
      rw [← unit_smul f R M V r m]
      exact (g.app ((Opens.map f).op.obj V)).hom.map_smul _ _)

private theorem forward_eq_original {M : PresheafOfModules.{v} R}
    {N : PresheafOfModules.{v} ((Opens.map f).op.pointwiseLeftKanExtension R)}
    (g : (inverseImageFunctor f R).obj M ⟶ N) :
    forward f R g = PresheafOfModules.homMk (forwardUnderlying f R g)
      (forwardUnderlying_smul f R g) := rfl

/-- The native Kan descent, shown linear over every pointwise-colimit ring section. -/
noncomputable def backward {M : PresheafOfModules.{v} R}
    {N : PresheafOfModules.{v} ((Opens.map f).op.pointwiseLeftKanExtension R)}
    (h : M ⟶ (PresheafOfModules.pushforward (F := Opens.map f)
      ((Opens.map f).op.pointwiseLeftKanExtensionUnit R)).obj N) :
    (inverseImageFunctor f R).obj M ⟶ N :=
  PresheafOfModules.homMk
    (((Opens.map f).op.pointwiseLeftKanExtension M.presheaf).descOfIsLeftKanExtension
      ((Opens.map f).op.pointwiseLeftKanExtensionUnit M.presheaf) N.presheaf
      ((PresheafOfModules.toPresheaf R).map h ≫
        ((PresheafOfModules.pushforwardCompToPresheaf (F := Opens.map f)
          ((Opens.map f).op.pointwiseLeftKanExtensionUnit R)).app N).hom))
    (by
      intro U r m
      obtain ⟨i, a, b, ha, hb⟩ :=
        pointwise_jointly_surjective f R M (unop U) r m
      subst r
      subst m
      erw [← pointwise_smul_ι f R M (unop U) i a b]
      erw [backwardUnderlying_ι f R h (unop U) i (a • b),
        backwardUnderlying_ι f R h (unop U) i b]
      erw [ring_ι_eq_map_unit f R (unop U) i a]
      change N.map i.hom (h.app i.left (a • b)) =
        (((Opens.map f).op.pointwiseLeftKanExtension R).map i.hom
          (((Opens.map f).op.pointwiseLeftKanExtensionUnit R).app i.left a)) •
          N.map i.hom (h.app i.left b)
      rw [map_smul]
      exact N.map_smul i.hom
        (((Opens.map f).op.pointwiseLeftKanExtensionUnit R).app i.left a)
        (h.app i.left b))

private theorem backward_eq_original {M : PresheafOfModules.{v} R}
    {N : PresheafOfModules.{v} ((Opens.map f).op.pointwiseLeftKanExtension R)}
    (h : M ⟶ (PresheafOfModules.pushforward (F := Opens.map f)
      ((Opens.map f).op.pointwiseLeftKanExtensionUnit R)).obj N)
    (U : (Opens X)ᵒᵖ) (m : (inverseImageFunctor f R |>.obj M).obj U) :
    (backward f R h).app U m = (backwardUnderlying f R h).app U m := rfl

/-- Kan descent is linear over every coefficient of the actual pointwise Kan ring. -/
theorem backward_smul {M : PresheafOfModules.{v} R}
    {N : PresheafOfModules.{v} ((Opens.map f).op.pointwiseLeftKanExtension R)}
    (h : M ⟶ (PresheafOfModules.pushforward (F := Opens.map f)
      ((Opens.map f).op.pointwiseLeftKanExtensionUnit R)).obj N)
    (U : (Opens X)ᵒᵖ)
    (r : ((Opens.map f).op.pointwiseLeftKanExtension R).obj U)
    (m : (inverseImageFunctor f R |>.obj M).obj U) :
    (backward f R h).app U (r • m) = r • (backward f R h).app U m :=
  backwardUnderlying_smul f R h U r m

theorem backward_ι {M : PresheafOfModules.{v} R}
    {N : PresheafOfModules.{v} ((Opens.map f).op.pointwiseLeftKanExtension R)}
    (h : M ⟶ (PresheafOfModules.pushforward (F := Opens.map f)
      ((Opens.map f).op.pointwiseLeftKanExtensionUnit R)).obj N)
    (U : Opens X) (i : index f U) (m : M.obj i.left) :
    (backward f R h).app (op U)
      ((colimit.ι (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ M.presheaf) i) m) =
    N.map i.hom (h.app i.left m) :=
  backwardUnderlying_ι f R h U i m

theorem forward_apply {M : PresheafOfModules.{v} R}
    {N : PresheafOfModules.{v} ((Opens.map f).op.pointwiseLeftKanExtension R)}
    (g : (inverseImageFunctor f R).obj M ⟶ N)
    (V : (Opens Y)ᵒᵖ) (m : M.obj V) :
    (forward f R g).app V m =
      g.app ((Opens.map f).op.obj V)
        (((Opens.map f).op.pointwiseLeftKanExtensionUnit M.presheaf).app V m) :=
  forwardUnderlying_apply f R g V m

theorem backward_forward {M : PresheafOfModules.{v} R}
    {N : PresheafOfModules.{v} ((Opens.map f).op.pointwiseLeftKanExtension R)}
    (g : (inverseImageFunctor f R).obj M ⟶ N) :
    backward f R (forward f R g) = g := by
  apply (PresheafOfModules.toPresheaf _).map_injective
  change backwardUnderlying f R (forward f R g) =
    (PresheafOfModules.toPresheaf _).map g
  apply (((Opens.map f).op.pointwiseLeftKanExtension M.presheaf).hom_ext_of_isLeftKanExtension
    ((Opens.map f).op.pointwiseLeftKanExtensionUnit M.presheaf))
  erw [Functor.descOfIsLeftKanExtension_fac]
  change forwardUnderlying f R g ≫
    ((PresheafOfModules.pushforwardCompToPresheaf (F := Opens.map f)
      ((Opens.map f).op.pointwiseLeftKanExtensionUnit R)).app N).hom =
    (Opens.map f).op.pointwiseLeftKanExtensionUnit M.presheaf ≫
      (Opens.map f).op.whiskerLeft
        ((PresheafOfModules.toPresheaf _).map g)
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro m
  rfl

theorem forward_backward {M : PresheafOfModules.{v} R}
    {N : PresheafOfModules.{v} ((Opens.map f).op.pointwiseLeftKanExtension R)}
    (h : M ⟶ (PresheafOfModules.pushforward (F := Opens.map f)
      ((Opens.map f).op.pointwiseLeftKanExtensionUnit R)).obj N) :
    forward f R (backward f R h) = h := by
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  rw [forward_apply f R (backward f R h) V m]
  let i : index f
      ((Opens.map f).obj (unop V)) :=
    CostructuredArrow.mk (𝟙 ((Opens.map f).op.obj V))
  change (backward f R h).app ((Opens.map f).op.obj V)
      ((colimit.ι (CostructuredArrow.proj (Opens.map f).op
        ((Opens.map f).op.obj V) ⋙ M.presheaf) i) m) = h.app V m
  erw [backward_ι f R h _ i m]
  change N.map (𝟙 _) (h.app V m) = h.app V m
  rw [N.map_id]
  rfl

/-- Naturality in the source module, for complete bundled linear maps. -/
theorem forward_naturality_left {M' M : PresheafOfModules.{v} R}
    {N : PresheafOfModules.{v} ((Opens.map f).op.pointwiseLeftKanExtension R)}
    (φ : M' ⟶ M) (g : (inverseImageFunctor f R).obj M ⟶ N) :
    forward f R ((inverseImageFunctor f R).map φ ≫ g) =
      φ ≫ forward f R g := by
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  rw [forward_apply f R ((inverseImageFunctor f R).map φ ≫ g) V m]
  change g.app ((Opens.map f).op.obj V)
      ((pointwiseMap f φ).app ((Opens.map f).op.obj V)
        (((Opens.map f).op.pointwiseLeftKanExtensionUnit M'.presheaf).app V m)) =
    (forward f R g).app V (φ.app V m)
  rw [forward_apply f R g V (φ.app V m)]
  have hunit := CategoryTheory.congr_fun
    (NatTrans.congr_app (pointwiseMap_unit f φ) V) m
  change (pointwiseMap f φ).app ((Opens.map f).op.obj V)
      (((Opens.map f).op.pointwiseLeftKanExtensionUnit M'.presheaf).app V m) =
    ((Opens.map f).op.pointwiseLeftKanExtensionUnit M.presheaf).app V (φ.app V m)
    at hunit
  rw [hunit]

/-- Naturality in the target module, for complete bundled linear maps. -/
theorem forward_naturality_right {M : PresheafOfModules.{v} R}
    {N N' : PresheafOfModules.{v} ((Opens.map f).op.pointwiseLeftKanExtension R)}
    (g : (inverseImageFunctor f R).obj M ⟶ N)
    (ψ : N ⟶ N') :
    forward f R (g ≫ ψ) =
      forward f R g ≫ (PresheafOfModules.pushforward (F := Opens.map f)
        ((Opens.map f).op.pointwiseLeftKanExtensionUnit R)).map ψ := by
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  rw [forward_apply f R (g ≫ ψ) V m]
  change ψ.app ((Opens.map f).op.obj V)
      (g.app ((Opens.map f).op.obj V)
        (((Opens.map f).op.pointwiseLeftKanExtensionUnit M.presheaf).app V m)) =
    ψ.app ((Opens.map f).op.obj V) ((forward f R g).app V m)
  rw [forward_apply f R g V m]

/-- The full presheaf-module Hom equivalence for the actual neighborhood-colimit action. -/
noncomputable def homEquiv (M : PresheafOfModules.{v} R)
    (N : PresheafOfModules.{v} ((Opens.map f).op.pointwiseLeftKanExtension R)) :
    ((inverseImageFunctor f R).obj M ⟶ N) ≃
      (M ⟶ (PresheafOfModules.pushforward (F := Opens.map f)
        ((Opens.map f).op.pointwiseLeftKanExtensionUnit R)).obj N) where
  toFun := forward f R
  invFun := backward f R
  left_inv := backward_forward f R
  right_inv := forward_backward f R

/-- The constructed equivalence is natural on both sides. -/
private noncomputable def homEquivCore : Adjunction.CoreHomEquiv
    (inverseImageFunctor f R)
    (PresheafOfModules.pushforward (F := Opens.map f)
      ((Opens.map f).op.pointwiseLeftKanExtensionUnit R)) where
  homEquiv := homEquiv f R
  homEquiv_naturality_left_symm := by
    intro M' M N φ h
    apply (homEquiv f R M' N).injective
    change forward f R (backward f R (φ ≫ h)) = forward f R
      ((inverseImageFunctor f R).map φ ≫ backward f R h)
    rw [forward_backward f R (φ ≫ h), forward_naturality_left f R φ,
      forward_backward f R h]
  homEquiv_naturality_right := by
    intro M N N' g ψ
    exact forward_naturality_right f R g ψ

/-- The actual neighborhood-colimit inverse-image functor is left adjoint to native pushforward. -/
noncomputable def adjunction : inverseImageFunctor f R ⊣
    PresheafOfModules.pushforward (F := Opens.map f)
      ((Opens.map f).op.pointwiseLeftKanExtensionUnit R) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv f R
      homEquiv_naturality_left_symm := by
        intro M' M N φ h
        apply (homEquiv f R M' N).injective
        change forward f R (backward f R (φ ≫ h)) = forward f R
          ((inverseImageFunctor f R).map φ ≫ backward f R h)
        rw [forward_backward f R (φ ≫ h), forward_naturality_left f R φ,
          forward_backward f R h]
      homEquiv_naturality_right := by
        intro M N N' g ψ
        exact forward_naturality_right f R g ψ }

private theorem adjunction_eq_original :
    adjunction f R = Adjunction.mkOfHomEquiv (homEquivCore f R) := rfl

/-- Naturality of descent with respect to the source module. -/
theorem backward_naturality_left {M' M : PresheafOfModules.{v} R}
    {N : PresheafOfModules.{v} ((Opens.map f).op.pointwiseLeftKanExtension R)}
    (φ : M' ⟶ M)
    (h : M ⟶ (PresheafOfModules.pushforward (F := Opens.map f)
      ((Opens.map f).op.pointwiseLeftKanExtensionUnit R)).obj N) :
    backward f R (φ ≫ h) =
      (inverseImageFunctor f R).map φ ≫ backward f R h :=
  (homEquivCore f R).homEquiv_naturality_left_symm φ h

/-- Naturality of descent with respect to the target module. -/
theorem backward_naturality_right {M : PresheafOfModules.{v} R}
    {N N' : PresheafOfModules.{v} ((Opens.map f).op.pointwiseLeftKanExtension R)}
    (h : M ⟶ (PresheafOfModules.pushforward (F := Opens.map f)
      ((Opens.map f).op.pointwiseLeftKanExtensionUnit R)).obj N)
    (ψ : N ⟶ N') :
    backward f R (h ≫ (PresheafOfModules.pushforward (F := Opens.map f)
      ((Opens.map f).op.pointwiseLeftKanExtensionUnit R)).map ψ) =
      backward f R h ≫ ψ :=
  (homEquivCore f R).homEquiv_naturality_right_symm h ψ

/-- The actual unit is the additive Kan unit, bundled as a linear map. -/
theorem unit_app_eq (M : PresheafOfModules.{v} R) :
    (adjunction f R).unit.app M =
      forward f R (𝟙 ((inverseImageFunctor f R).obj M)) := rfl

theorem unit_apply (M : PresheafOfModules.{v} R) (V : (Opens Y)ᵒᵖ)
    (m : M.obj V) :
    ((adjunction f R).unit.app M).app V m =
      ((Opens.map f).op.pointwiseLeftKanExtensionUnit M.presheaf).app V m := by
  rw [unit_app_eq f R M, forward_apply f R]
  rfl

/-- The actual counit is Kan descent of the pushforward identity. -/
theorem counit_app_eq
    (N : PresheafOfModules.{v} ((Opens.map f).op.pointwiseLeftKanExtension R)) :
    (adjunction f R).counit.app N =
      backward f R (𝟙 ((PresheafOfModules.pushforward (F := Opens.map f)
        ((Opens.map f).op.pointwiseLeftKanExtensionUnit R)).obj N)) := rfl

theorem counit_ι
    (N : PresheafOfModules.{v} ((Opens.map f).op.pointwiseLeftKanExtension R))
    (U : Opens X) (i : index f U)
    (m : ((PresheafOfModules.pushforward (F := Opens.map f)
      ((Opens.map f).op.pointwiseLeftKanExtensionUnit R)).obj N).obj i.left) :
    ((adjunction f R).counit.app N).app (op U)
      ((colimit.ι (CostructuredArrow.proj (Opens.map f).op (op U) ⋙
        ((PresheafOfModules.pushforward (F := Opens.map f)
          ((Opens.map f).op.pointwiseLeftKanExtensionUnit R)).obj N).presheaf) i) m) =
    N.map i.hom m := by
  rw [counit_app_eq f R N, backward_ι f R]
  rfl

theorem unit_naturality {M M' : PresheafOfModules.{v} R} (φ : M ⟶ M') :
    φ ≫ (adjunction f R).unit.app M' =
      (adjunction f R).unit.app M ≫
        ((inverseImageFunctor f R) ⋙
          (PresheafOfModules.pushforward (F := Opens.map f)
            ((Opens.map f).op.pointwiseLeftKanExtensionUnit R))).map φ :=
  (adjunction f R).unit.naturality φ

theorem counit_naturality
    {N N' : PresheafOfModules.{v} ((Opens.map f).op.pointwiseLeftKanExtension R)}
    (ψ : N ⟶ N') :
    ((PresheafOfModules.pushforward (F := Opens.map f)
      ((Opens.map f).op.pointwiseLeftKanExtensionUnit R)) ⋙
      inverseImageFunctor f R).map ψ ≫
        (adjunction f R).counit.app N' =
      (adjunction f R).counit.app N ≫ ψ :=
  (adjunction f R).counit.naturality ψ

set_option backward.isDefEq.respectTransparency false in
/-- The forward map is the ordinary additive presheaf transpose, after the accepted
pointwise-to-native pullback comparison in the inverse direction. -/
theorem forward_underlying_additive {M : PresheafOfModules.{v} R}
    {N : PresheafOfModules.{v} ((Opens.map f).op.pointwiseLeftKanExtension R)}
    (g : (inverseImageFunctor f R).obj M ⟶ N) :
    (PresheafOfModules.toPresheaf R).map (forward f R g) ≫
      ((PresheafOfModules.pushforwardCompToPresheaf (F := Opens.map f)
        ((Opens.map f).op.pointwiseLeftKanExtensionUnit R)).app N).hom =
    (TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{v} f).homEquiv
      M.presheaf N.presheaf
      ((underlyingComparison f R).inv.app M ≫
        (PresheafOfModules.toPresheaf _).map g) := by
  change (PresheafOfModules.toPresheaf R).map (forward f R g) ≫
      ((PresheafOfModules.pushforwardCompToPresheaf (F := Opens.map f)
        ((Opens.map f).op.pointwiseLeftKanExtensionUnit R)).app N).hom =
    (Opens.map f).op.leftKanExtensionUnit M.presheaf ≫
      (Opens.map f).op.whiskerLeft
        ((pointwiseToPullback f AddCommGrpCat.{v} M.presheaf).inv ≫
          (PresheafOfModules.toPresheaf _).map g)
  calc
    _ = (Opens.map f).op.pointwiseLeftKanExtensionUnit M.presheaf ≫
        (Opens.map f).op.whiskerLeft (PresheafOfModules.toPresheaf _ |>.map g) := by
      apply NatTrans.ext
      funext V
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro m
      rfl
    _ = (Opens.map f).op.leftKanExtensionUnit M.presheaf ≫
        (Opens.map f).op.whiskerLeft
          ((pointwiseToPullback f AddCommGrpCat.{v} M.presheaf).inv ≫
            (PresheafOfModules.toPresheaf _).map g) := by
      let e := pointwiseToPullback f AddCommGrpCat.{v} M.presheaf
      let γ := (PresheafOfModules.toPresheaf
        ((Opens.map f).op.pointwiseLeftKanExtension R)).map g
      calc
        _ = (Opens.map f).op.pointwiseLeftKanExtensionUnit M.presheaf ≫
            (Opens.map f).op.whiskerLeft ((e.hom ≫ e.inv) ≫ γ) := by
              rw [Iso.hom_inv_id, Category.id_comp]
        _ = ((Opens.map f).op.pointwiseLeftKanExtensionUnit M.presheaf ≫
            (Opens.map f).op.whiskerLeft e.hom) ≫
              (Opens.map f).op.whiskerLeft (e.inv ≫ γ) := by
                simp only [Category.assoc, Functor.whiskerLeft_comp]
        _ = _ := by rw [pointwiseToPullback_fac f M.presheaf]

end RingedSpaces.Modules.PresheafInverseImage

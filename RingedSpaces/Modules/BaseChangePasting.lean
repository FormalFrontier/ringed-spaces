/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import RingedSpaces.Modules.BaseChange

/-!
# Pasting ringed-space module base-change comparisons

For arbitrary commutative squares of full ringed-space morphisms, the mate of
the outer square equals the composite of the mates of the two inner squares.
The functor comparisons are the canonical composition isomorphisms of the
actual sheafified inverse image and full direct image.
-/

set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

@[expose] public section

namespace RingedSpaces.Modules.BaseChange

open CategoryTheory CategoryTheory.Functor CategoryTheory.TwoSquare PullbackCoherence

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

private theorem mateEquiv_whiskerTop
    {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
    {source source' : C ⥤ E} {target : D ⥤ F}
    {left : C ⥤ D} {leftRight : D ⥤ C} {right : E ⥤ F} {rightRight : F ⥤ E}
    (adj₁ : left ⊣ leftRight) (adj₂ : right ⊣ rightRight)
    (comparison : TwoSquare source left right target) (changeSource : source' ⟶ source) :
    mateEquiv adj₁ adj₂ (comparison.whiskerTop changeSource) =
      whiskerLeft leftRight changeSource ≫ mateEquiv adj₁ adj₂ comparison := by
  ext object
  simp [mateEquiv, TwoSquare.whiskerTop, Category.assoc]

private theorem mateEquiv_whiskerBottom
    {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
    {source : C ⥤ E} {target target' : D ⥤ F}
    {left : C ⥤ D} {leftRight : D ⥤ C} {right : E ⥤ F} {rightRight : F ⥤ E}
    (adj₁ : left ⊣ leftRight) (adj₂ : right ⊣ rightRight)
    (comparison : TwoSquare source left right target) (changeTarget : target ⟶ target') :
    mateEquiv adj₁ adj₂ (comparison.whiskerBottom changeTarget) =
      (mateEquiv adj₁ adj₂ comparison).whiskerLeft changeTarget := by
  ext object
  simp only [mateEquiv, TwoSquare.whiskerBottom, TwoSquare.whiskerLeft,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_obj, Functor.comp_map, Category.assoc, Equiv.coe_fn_mk,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Functor.map_comp]
  have natural := congrArg (fun arrow =>
    adj₂.unit.app (source.obj (leftRight.obj object)) ≫
      rightRight.map (comparison.natTrans.app (leftRight.obj object)) ≫ rightRight.map arrow)
      (changeTarget.naturality (adj₁.counit.app object)).symm
  simpa only [Functor.comp_obj, Functor.id_obj, Category.id_comp, Category.comp_id,
    Functor.map_comp, Category.assoc] using natural

universe uu vv

section PastedSquares

variable {C₁ C₂ C₃ C₄ C₅ C₆ : Type uu}
  [Category.{vv} C₁] [Category.{vv} C₂] [Category.{vv} C₃]
  [Category.{vv} C₄] [Category.{vv} C₅] [Category.{vv} C₆]
variable {top : C₁ ⥤ C₂} {left : C₁ ⥤ C₃} {right : C₂ ⥤ C₄}
  {bottom : C₃ ⥤ C₄} {left' : C₃ ⥤ C₅} {right' : C₄ ⥤ C₆}
  {bottom' : C₅ ⥤ C₆}

private theorem pastedSquares_hom_inv (first : top ⋙ right ≅ left ⋙ bottom)
    (second : bottom ⋙ right' ≅ left' ⋙ bottom') :
    (first.hom ≫ᵥ second.hom) ≫ (first.inv ≫ₕ second.inv) =
      𝟙 (top ⋙ (right ⋙ right')) := by
  ext object
  simp [TwoSquare.vComp, TwoSquare.hComp, Category.assoc]

private theorem pastedSquares_inv_hom (first : top ⋙ right ≅ left ⋙ bottom)
    (second : bottom ⋙ right' ≅ left' ⋙ bottom') :
    (first.inv ≫ₕ second.inv) ≫ (first.hom ≫ᵥ second.hom) =
      𝟙 ((left ⋙ left') ⋙ bottom') := by
  ext object
  simp only [TwoSquare.vComp, TwoSquare.hComp, TwoSquare.natTrans,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.comp_obj, Category.assoc, NatTrans.id_app]
  simp only [Category.id_comp, Category.comp_id]
  calc
    _ = second.inv.app (left.obj object) ≫
          right'.map ((first.inv ≫ first.hom).app object) ≫
          second.hom.app (left.obj object) := by
        simp only [NatTrans.comp_app, Functor.map_comp, Category.assoc]
    _ = _ := by simp

end PastedSquares

universe u

variable {W₀ W₁ W₂ Z₀ Z₁ Z₂ : AlgebraicGeometry.RingedSpace.{u, u}}

variable {X₀ X₁ X₂ : AlgebraicGeometry.RingedSpace.{u, u}}

private theorem pushforwardComp_congr_left {V X Y : AlgebraicGeometry.RingedSpace.{u, u}}
    {f f' : V ⟶ X} (g : X ⟶ Y) (e : f = f') :
    (isoWhiskerRight (eqToIso (congrArg R e)) (R g)).hom ≫
        (pushforwardComp f' g).hom =
      (pushforwardComp f g).hom ≫
        (eqToIso (congrArg R (congrArg (fun i => i ≫ g) e))).hom := by
  cases e
  simp

private theorem pushforwardComp_congr_right {V X Y : AlgebraicGeometry.RingedSpace.{u, u}}
    (f : V ⟶ X) {g g' : X ⟶ Y} (e : g = g') :
    (isoWhiskerLeft (R f) (eqToIso (congrArg R e))).hom ≫
        (pushforwardComp f g').hom =
      (pushforwardComp f g).hom ≫
        (eqToIso (congrArg R (congrArg (fun i => f ≫ i) e))).hom := by
  cases e
  simp

private theorem pushforwardComp_assoc_cut {V X Y Z : AlgebraicGeometry.RingedSpace.{u, u}}
    (f : V ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (isoWhiskerLeft (R f) (pushforwardComp g h)).inv ≫
        (associator (R f) (R g) (R h)).inv ≫
        whiskerRight (pushforwardComp f g).hom (R h) =
      (pushforwardComp f (g ≫ h)).hom ≫ (pushforwardComp (f ≫ g) h).inv := by
  have coherence := congrArg (fun iso => iso.hom) (pushforwardComp_assoc f g h)
  simp only [Iso.trans_hom, Iso.symm_hom, isoWhiskerLeft_hom,
    isoWhiskerRight_hom] at coherence
  simp only [isoWhiskerLeft_inv]
  apply (Iso.inv_comp_eq (isoWhiskerLeft (R f) (pushforwardComp g h))).2
  rw [eq_comm]
  conv_lhs => rw [← Category.assoc]
  apply (Iso.comp_inv_eq (pushforwardComp (f ≫ g) h)).2
  simpa only [isoWhiskerLeft_hom, Category.assoc] using coherence

private theorem pushforwardComp_path {V X : AlgebraicGeometry.RingedSpace.{u, u}}
    {f g k : V ⟶ X} (first : f = g) (second : g = k) (outer : f = k) :
    (eqToIso (congrArg R outer)).hom =
      (eqToIso (congrArg R first)).hom ≫
        (eqToIso (congrArg R second)).hom := by
  cases first
  cases second
  cases outer
  simp

private theorem pushforwardSquare_flip
    {V X Y Z : AlgebraicGeometry.RingedSpace.{u, u}}
    (bottom : V ⟶ X) (left : V ⟶ Y) (top : X ⟶ Z) (right : Y ⟶ Z)
    (commutes : bottom ≫ top = left ≫ right) :
    pushforwardSquare bottom left top right commutes =
      (pushforwardSquare left bottom right top commutes.symm).symm := by
  have transport : (eqToIso (congrArg R commutes)) =
      (eqToIso (congrArg R commutes.symm)).symm := by
    have general {first second : V ⟶ Z} (equality : first = second) :
        (eqToIso (congrArg R equality)) =
          (eqToIso (congrArg R equality.symm)).symm := by
      cases equality
      simp
    exact general commutes
  simp [pushforwardSquare, Iso.trans_symm, transport]

private theorem pushforwardSquare_pastePushforward (a₀ : W₀ ⟶ X₀) (a₁ : W₁ ⟶ X₁)
    (a₂ : W₂ ⟶ X₂) (v₀ : W₀ ⟶ W₁) (v₁ : W₁ ⟶ W₂)
    (w₀ : X₀ ⟶ X₁) (w₁ : X₁ ⟶ X₂)
    (h₀ : a₀ ≫ w₀ = v₀ ≫ a₁) (h₁ : a₁ ≫ w₁ = v₁ ≫ a₂)
    (h : a₀ ≫ (w₀ ≫ w₁) = (v₀ ≫ v₁) ≫ a₂) :
    (pushforwardSquare a₀ (v₀ ≫ v₁) (w₀ ≫ w₁) a₂ h).hom =
      (isoWhiskerLeft (R a₀) (pushforwardComp w₀ w₁)).inv ≫
      ((pushforwardSquare a₀ v₀ w₀ a₁ h₀).hom ≫ᵥ
        (pushforwardSquare a₁ v₁ w₁ a₂ h₁).hom) ≫
      (isoWhiskerRight (pushforwardComp v₀ v₁) (R a₂)).hom := by
  have congrLeft := pushforwardComp_congr_left w₁ h₀
  have congrRight := pushforwardComp_congr_right v₀ h₁
  have topCut := pushforwardComp_assoc_cut a₀ w₀ w₁
  have middle := congrArg (fun iso => iso.hom) (pushforwardComp_assoc v₀ a₁ w₁)
  simp only [Iso.trans_hom, Iso.symm_hom, isoWhiskerLeft_hom,
    isoWhiskerRight_hom] at middle
  have middleCut :
      (pushforwardComp (v₀ ≫ a₁) w₁).inv ≫
          whiskerRight (pushforwardComp v₀ a₁).inv (R w₁) ≫
          (associator (R v₀) (R a₁) (R w₁)).hom ≫
          (isoWhiskerLeft (R v₀) (pushforwardComp a₁ w₁)).hom =
        (pushforwardComp v₀ (a₁ ≫ w₁)).inv := by
    simp only [isoWhiskerLeft_hom]
    apply (Iso.inv_comp_eq (pushforwardComp (v₀ ≫ a₁) w₁)).2
    rw [eq_comm]
    apply (Iso.comp_inv_eq (pushforwardComp v₀ (a₁ ≫ w₁))).2
    rw [eq_comm]
    conv_lhs => rw [Category.assoc]
    apply (Iso.inv_comp_eq
      (isoWhiskerRight (pushforwardComp v₀ a₁) (R w₁))).2
    simpa only [isoWhiskerRight_hom, Category.assoc] using
      ((Iso.inv_comp_eq (associator (R v₀) (R a₁) (R w₁))).1 middle.symm).symm
  have bottomCut := pushforwardComp_assoc_cut v₀ v₁ a₂
  simp only [pushforwardSquare, Iso.trans_hom, Iso.symm_hom,
    TwoSquare.vComp, whiskerRight_comp, whiskerLeft_comp]
  dsimp only [TwoSquare.mk]
  rw [eq_comm]
  let bridge₀ : R (a₀ ≫ w₀) ⋙ R w₁ ⟶ R v₀ ⋙ R (a₁ ≫ w₁) :=
    whiskerRight (eqToIso (congrArg R h₀)).hom (R w₁) ≫
    whiskerRight (pushforwardComp v₀ a₁).inv (R w₁) ≫
    (associator (R v₀) (R a₁) (R w₁)).hom ≫
    whiskerLeft (R v₀) (pushforwardComp a₁ w₁).hom
  let bridge₁ : R v₀ ⋙ R (a₁ ≫ w₁) ⟶ R (v₀ ≫ v₁) ⋙ R a₂ :=
    whiskerLeft (R v₀) (eqToIso (congrArg R h₁)).hom ≫
    whiskerLeft (R v₀) (pushforwardComp v₁ a₂).inv ≫
    (associator (R v₀) (R v₁) (R a₂)).inv ≫
    (isoWhiskerRight (pushforwardComp v₀ v₁) (R a₂)).hom
  let tail := bridge₀ ≫ bridge₁
  have firstBridge :
      (pushforwardComp (a₀ ≫ w₀) w₁).inv ≫ bridge₀ =
        (eqToIso (congrArg R (congrArg (fun arrow => arrow ≫ w₁) h₀))).hom ≫
          (pushforwardComp v₀ (a₁ ≫ w₁)).inv := by
    let eqWhisker := whiskerRight (eqToIso (congrArg R h₀)).hom (R w₁)
    let innerMiddle := whiskerRight (pushforwardComp v₀ a₁).inv (R w₁) ≫
      (associator (R v₀) (R a₁) (R w₁)).hom ≫
      whiskerLeft (R v₀) (pushforwardComp a₁ w₁).hom
    have middleFact : (pushforwardComp (v₀ ≫ a₁) w₁).inv ≫ innerMiddle =
        (pushforwardComp v₀ (a₁ ≫ w₁)).inv := by
      simpa only [innerMiddle, isoWhiskerLeft_hom, Category.assoc] using middleCut
    calc
      _ = (pushforwardComp (a₀ ≫ w₀) w₁).inv ≫
            (eqWhisker ≫ (pushforwardComp (v₀ ≫ a₁) w₁).hom) ≫
            ((pushforwardComp (v₀ ≫ a₁) w₁).inv ≫ innerMiddle) := by
          simp only [bridge₀, eqWhisker, innerMiddle, Category.assoc,
            Iso.hom_inv_id_assoc]
      _ = (pushforwardComp (a₀ ≫ w₀) w₁).inv ≫
            ((pushforwardComp (a₀ ≫ w₀) w₁).hom ≫
              (eqToIso (congrArg R (congrArg (fun arrow => arrow ≫ w₁) h₀))).hom) ≫
            (pushforwardComp v₀ (a₁ ≫ w₁)).inv := by
          simpa only [eqWhisker, isoWhiskerRight_hom, middleFact] using
            congrArg (fun arrow => (pushforwardComp (a₀ ≫ w₀) w₁).inv ≫
              arrow ≫ (pushforwardComp v₀ (a₁ ≫ w₁)).inv) congrLeft
      _ = _ := by simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have secondBridge :
      (pushforwardComp v₀ (a₁ ≫ w₁)).inv ≫ bridge₁ =
        (eqToIso (congrArg R (congrArg (fun arrow => v₀ ≫ arrow) h₁))).hom ≫
          (pushforwardComp (v₀ ≫ v₁) a₂).inv := by
    let eqWhisker := whiskerLeft (R v₀) (eqToIso (congrArg R h₁)).hom
    calc
      _ = (pushforwardComp v₀ (a₁ ≫ w₁)).inv ≫ eqWhisker ≫
            ((isoWhiskerLeft (R v₀) (pushforwardComp v₁ a₂)).inv ≫
              (associator (R v₀) (R v₁) (R a₂)).inv ≫
              whiskerRight (pushforwardComp v₀ v₁).hom (R a₂)) := by
          simp only [bridge₁, eqWhisker, isoWhiskerLeft_inv, isoWhiskerRight_hom,
            ]
      _ = (pushforwardComp v₀ (a₁ ≫ w₁)).inv ≫ eqWhisker ≫
            ((pushforwardComp v₀ (v₁ ≫ a₂)).hom ≫
              (pushforwardComp (v₀ ≫ v₁) a₂).inv) :=
          congrArg (fun arrow => (pushforwardComp v₀ (a₁ ≫ w₁)).inv ≫
            eqWhisker ≫ arrow) bottomCut
      _ = (pushforwardComp v₀ (a₁ ≫ w₁)).inv ≫
            ((pushforwardComp v₀ (a₁ ≫ w₁)).hom ≫
              (eqToIso (congrArg R (congrArg (fun arrow => v₀ ≫ arrow) h₁))).hom) ≫
            (pushforwardComp (v₀ ≫ v₁) a₂).inv := by
          simpa only [eqWhisker, isoWhiskerLeft_hom, Category.assoc] using
            congrArg (fun arrow => (pushforwardComp v₀ (a₁ ≫ w₁)).inv ≫
              arrow ≫ (pushforwardComp (v₀ ≫ v₁) a₂).inv) congrRight
      _ = _ := by simp [Category.assoc]
  have combined :
      (pushforwardComp (a₀ ≫ w₀) w₁).inv ≫ tail =
        (eqToIso (congrArg R h)).hom ≫
          (pushforwardComp (v₀ ≫ v₁) a₂).inv := by
    have paths := pushforwardComp_path
      (congrArg (fun arrow => arrow ≫ w₁) h₀)
      (congrArg (fun arrow => v₀ ≫ arrow) h₁) h
    calc
      _ = ((pushforwardComp (a₀ ≫ w₀) w₁).inv ≫ bridge₀) ≫ bridge₁ := by
        simp only [tail, Category.assoc]
      _ = ((eqToIso (congrArg R (congrArg (fun arrow => arrow ≫ w₁) h₀))).hom ≫
          (pushforwardComp v₀ (a₁ ≫ w₁)).inv) ≫ bridge₁ :=
        congrArg (fun arrow => arrow ≫ bridge₁) firstBridge
      _ = (eqToIso (congrArg R (congrArg (fun arrow => arrow ≫ w₁) h₀))).hom ≫
          ((pushforwardComp v₀ (a₁ ≫ w₁)).inv ≫ bridge₁) :=
        Category.assoc _ _ _
      _ = (eqToIso (congrArg R (congrArg (fun arrow => arrow ≫ w₁) h₀))).hom ≫
          ((eqToIso (congrArg R (congrArg (fun arrow => v₀ ≫ arrow) h₁))).hom ≫
            (pushforwardComp (v₀ ≫ v₁) a₂).inv) :=
        congrArg (fun arrow =>
          (eqToIso (congrArg R (congrArg (fun arrow => arrow ≫ w₁) h₀))).hom ≫ arrow)
          secondBridge
      _ = _ := by
        simpa only [Category.assoc] using
          congrArg (fun arrow => arrow ≫ (pushforwardComp (v₀ ≫ v₁) a₂).inv)
            paths.symm
  calc
    _ = ((isoWhiskerLeft (R a₀) (pushforwardComp w₀ w₁)).inv ≫
        (associator (R a₀) (R w₀) (R w₁)).inv ≫
        whiskerRight (pushforwardComp a₀ w₀).hom (R w₁)) ≫ tail := by
      simp only [tail, bridge₀, bridge₁, Category.assoc]
    _ = ((pushforwardComp a₀ (w₀ ≫ w₁)).hom ≫
        (pushforwardComp (a₀ ≫ w₀) w₁).inv) ≫ tail :=
      congrArg (fun arrow => arrow ≫ tail) topCut
    _ = _ := by
      simpa only [Category.assoc] using
        congrArg (fun arrow => (pushforwardComp a₀ (w₀ ≫ w₁)).hom ≫ arrow) combined

/-- Pasting the vertical edges of
`W₀ ⟶ X₀`, `W₁ ⟶ X₁`, `W₂ ⟶ X₂` agrees with the actual outer-square mate.
The vertical edges occur as direct images in the source and target. -/
theorem pushPull_pastePushforward (a₀ : W₀ ⟶ X₀) (a₁ : W₁ ⟶ X₁)
    (a₂ : W₂ ⟶ X₂) (v₀ : W₀ ⟶ W₁) (v₁ : W₁ ⟶ W₂)
    (w₀ : X₀ ⟶ X₁) (w₁ : X₁ ⟶ X₂)
    (h₀ : a₀ ≫ w₀ = v₀ ≫ a₁) (h₁ : a₁ ≫ w₁ = v₁ ≫ a₂) :
    pushPull a₀ (v₀ ≫ v₁) (w₀ ≫ w₁) a₂
        (by
          calc
            a₀ ≫ (w₀ ≫ w₁) = (a₀ ≫ w₀) ≫ w₁ := (Category.assoc _ _ _).symm
            _ = (v₀ ≫ a₁) ≫ w₁ := by rw [h₀]
            _ = v₀ ≫ (a₁ ≫ w₁) := Category.assoc _ _ _
            _ = v₀ ≫ (v₁ ≫ a₂) := by rw [h₁]
            _ = (v₀ ≫ v₁) ≫ a₂ := (Category.assoc _ _ _).symm) =
      (isoWhiskerRight (pushforwardComp w₀ w₁) (L a₂)).inv ≫
      (associator (R w₀) (R w₁) (L a₂)).hom ≫
      whiskerLeft (R w₀) (pushPull a₁ v₁ w₁ a₂ h₁) ≫
      (associator (R w₀) (L a₁) (R v₁)).inv ≫
      whiskerRight (pushPull a₀ v₀ w₀ a₁ h₀) (R v₁) ≫
      (associator (L a₀) (R v₀) (R v₁)).hom ≫
      (isoWhiskerLeft (L a₀) (pushforwardComp v₀ v₁)).hom := by
  have pasted :
      mateEquiv (A a₀) (A a₂)
          (pushPull a₀ v₀ w₀ a₁ h₀ ≫ₕ pushPull a₁ v₁ w₁ a₂ h₁) =
        (pushforwardSquare a₀ v₀ w₀ a₁ h₀).hom ≫ᵥ
          (pushforwardSquare a₁ v₁ w₁ a₂ h₁).hom := by
    simpa only [pushPull, Equiv.apply_symm_apply] using
      (mateEquiv_vcomp (A a₀) (A a₁) (A a₂)
        (pushPull a₀ v₀ w₀ a₁ h₀) (pushPull a₁ v₁ w₁ a₂ h₁))
  have hOuter : a₀ ≫ (w₀ ≫ w₁) = (v₀ ≫ v₁) ≫ a₂ := by
    calc
      a₀ ≫ (w₀ ≫ w₁) = (a₀ ≫ w₀) ≫ w₁ := (Category.assoc _ _ _).symm
      _ = (v₀ ≫ a₁) ≫ w₁ := by rw [h₀]
      _ = v₀ ≫ (a₁ ≫ w₁) := Category.assoc _ _ _
      _ = v₀ ≫ (v₁ ≫ a₂) := by rw [h₁]
      _ = (v₀ ≫ v₁) ≫ a₂ := (Category.assoc _ _ _).symm
  have rightMate :
      mateEquiv (A a₀) (A a₂)
        (((pushPull a₀ v₀ w₀ a₁ h₀ ≫ₕ pushPull a₁ v₁ w₁ a₂ h₁).whiskerTop
          (pushforwardComp w₀ w₁).inv).whiskerBottom (pushforwardComp v₀ v₁).hom) =
          (pushforwardSquare a₀ (v₀ ≫ v₁) (w₀ ≫ w₁) a₂ hOuter).hom := by
    rw [mateEquiv_whiskerBottom, mateEquiv_whiskerTop, pasted]
    simpa only [TwoSquare.whiskerLeft, isoWhiskerLeft_inv,
      isoWhiskerRight_hom, Category.assoc] using
      (pushforwardSquare_pastePushforward a₀ a₁ a₂ v₀ v₁ w₀ w₁ h₀ h₁ hOuter).symm
  apply (mateEquiv (A a₀) (A a₂)).injective
  rw [pushPull, Equiv.apply_symm_apply]
  simpa only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
    TwoSquare.hComp, isoWhiskerRight_inv, isoWhiskerLeft_hom,
    Category.assoc] using rightMate.symm

private theorem pushforwardSquare_pastePullback (a₀₁ : W₀ ⟶ W₁) (a₁₂ : W₁ ⟶ W₂)
    (v₀ : W₀ ⟶ Z₀) (v₁ : W₁ ⟶ Z₁) (v₂ : W₂ ⟶ Z₂)
    (b₀₁ : Z₀ ⟶ Z₁) (b₁₂ : Z₁ ⟶ Z₂)
    (h₀₁ : a₀₁ ≫ v₁ = v₀ ≫ b₀₁) (h₁₂ : a₁₂ ≫ v₂ = v₁ ≫ b₁₂)
    (h : (a₀₁ ≫ a₁₂) ≫ v₂ = v₀ ≫ (b₀₁ ≫ b₁₂)) :
    (pushforwardSquare (a₀₁ ≫ a₁₂) v₀ v₂ (b₀₁ ≫ b₁₂) h).hom =
      (isoWhiskerRight (pushforwardComp a₀₁ a₁₂) (R v₂)).inv ≫
      ((pushforwardSquare a₀₁ v₀ v₁ b₀₁ h₀₁).hom ≫ₕ
        (pushforwardSquare a₁₂ v₁ v₂ b₁₂ h₁₂).hom) ≫
      (isoWhiskerLeft (R v₀) (pushforwardComp b₀₁ b₁₂)).hom := by
  have rotated := pushforwardSquare_pastePushforward v₀ v₁ v₂
    a₀₁ a₁₂ b₀₁ b₁₂ h₀₁.symm h₁₂.symm h.symm
  let first := pushforwardSquare v₀ a₀₁ b₀₁ v₁ h₀₁.symm
  let second := pushforwardSquare v₁ a₁₂ b₁₂ v₂ h₁₂.symm
  let outer := pushforwardSquare v₀ (a₀₁ ≫ a₁₂) (b₀₁ ≫ b₁₂) v₂ h.symm
  let leftIso := isoWhiskerLeft (R v₀) (pushforwardComp b₀₁ b₁₂)
  let rightIso := isoWhiskerRight (pushforwardComp a₀₁ a₁₂) (R v₂)
  let middleIso : R v₀ ⋙ (R b₀₁ ⋙ R b₁₂) ≅
      (R a₀₁ ⋙ R a₁₂) ⋙ R v₂ :=
    { hom := first.hom ≫ᵥ second.hom
      inv := first.inv ≫ₕ second.inv
      hom_inv_id := pastedSquares_hom_inv first second
      inv_hom_id := pastedSquares_inv_hom first second }
  have outerIso : outer = leftIso.symm ≪≫ middleIso ≪≫ rightIso := by
    apply Iso.ext
    simpa only [Iso.trans_hom, Iso.symm_hom, middleIso] using rotated
  have flipped := pushforwardSquare_flip (a₀₁ ≫ a₁₂) v₀ v₂
    (b₀₁ ≫ b₁₂) h
  have flipped₀ := pushforwardSquare_flip a₀₁ v₀ v₁ b₀₁ h₀₁
  have flipped₁ := pushforwardSquare_flip a₁₂ v₁ v₂ b₁₂ h₁₂
  rw [flipped, Iso.symm_hom]
  change outer.inv = _
  rw [outerIso]
  simp only [Iso.trans_inv, Iso.symm_inv, middleIso, leftIso, rightIso]
  rw [flipped₀, flipped₁]
  simp only [Iso.symm_hom]
  rfl

private theorem pullbackComp_forward_mate {V X Y : AlgebraicGeometry.RingedSpace.{u, u}}
    (f : V ⟶ X) (g : X ⟶ Y) :
    conjugateEquiv (A (f ≫ g)) ((A g).comp (A f)) (pullbackComp f g).hom =
      (pushforwardComp f g).inv := by
  apply (Iso.comp_hom_eq_id (pushforwardComp f g)).mp
  rw [← pullbackComp_inverse_mate]
  exact conjugateEquiv_comm (A (f ≫ g)) ((A g).comp (A f)) (by simp)

/-- Pasting the horizontal edges of
`W₀ ⟶ W₁ ⟶ W₂` over `Z₀ ⟶ Z₁ ⟶ Z₂` agrees with the actual outer-square mate.
The lower horizontal edges occur as inverse images in the source. -/
theorem pushPull_pastePullback (a₀₁ : W₀ ⟶ W₁) (a₁₂ : W₁ ⟶ W₂)
    (v₀ : W₀ ⟶ Z₀) (v₁ : W₁ ⟶ Z₁) (v₂ : W₂ ⟶ Z₂)
    (b₀₁ : Z₀ ⟶ Z₁) (b₁₂ : Z₁ ⟶ Z₂)
    (h₀₁ : a₀₁ ≫ v₁ = v₀ ≫ b₀₁) (h₁₂ : a₁₂ ≫ v₂ = v₁ ≫ b₁₂) :
    pushPull (a₀₁ ≫ a₁₂) v₀ v₂ (b₀₁ ≫ b₁₂)
        (by rw [Category.assoc, h₁₂, ← Category.assoc, h₀₁, Category.assoc]) =
      (isoWhiskerLeft (R v₂) (pullbackComp b₀₁ b₁₂)).inv ≫
      (associator (R v₂) (L b₁₂) (L b₀₁)).inv ≫
      whiskerRight (pushPull a₁₂ v₁ v₂ b₁₂ h₁₂) (L b₀₁) ≫
      (associator (L a₁₂) (R v₁) (L b₀₁)).hom ≫
      whiskerLeft (L a₁₂) (pushPull a₀₁ v₀ v₁ b₀₁ h₀₁) ≫
      (associator (L a₁₂) (L a₀₁) (R v₀)).inv ≫
      (isoWhiskerRight (pullbackComp a₀₁ a₁₂) (R v₀)).hom := by
  let pasted := pushPull a₁₂ v₁ v₂ b₁₂ h₁₂ ≫ᵥ pushPull a₀₁ v₀ v₁ b₀₁ h₀₁
  have hOuter : (a₀₁ ≫ a₁₂) ≫ v₂ = v₀ ≫ (b₀₁ ≫ b₁₂) := by
    rw [Category.assoc, h₁₂, ← Category.assoc, h₀₁, Category.assoc]
  have pastedMate :
      mateEquiv ((A a₁₂).comp (A a₀₁)) ((A b₁₂).comp (A b₀₁)) pasted =
        (pushforwardSquare a₀₁ v₀ v₁ b₀₁ h₀₁).hom ≫ₕ
          (pushforwardSquare a₁₂ v₁ v₂ b₁₂ h₁₂).hom := by
    simpa only [pasted, pushPull, Equiv.apply_symm_apply] using
      (mateEquiv_hcomp (A a₁₂) (A b₁₂) (A a₀₁) (A b₀₁)
        (pushPull a₁₂ v₁ v₂ b₁₂ h₁₂) (pushPull a₀₁ v₀ v₁ b₀₁ h₀₁))
  have moveRight :
      mateEquiv ((A a₁₂).comp (A a₀₁)) (A (b₀₁ ≫ b₁₂))
          (pasted.whiskerRight (pullbackComp b₀₁ b₁₂).inv) =
        (mateEquiv ((A a₁₂).comp (A a₀₁)) ((A b₁₂).comp (A b₀₁)) pasted).whiskerBottom
          (pushforwardComp b₀₁ b₁₂).hom := by
    rw [mateEquiv_conjugateEquiv_vcomp, pullbackComp_inverse_mate]
  have moveLeft :
      mateEquiv (A (a₀₁ ≫ a₁₂)) (A (b₀₁ ≫ b₁₂))
          ((pasted.whiskerRight (pullbackComp b₀₁ b₁₂).inv).whiskerLeft
            (pullbackComp a₀₁ a₁₂).hom) =
        (mateEquiv ((A a₁₂).comp (A a₀₁)) (A (b₀₁ ≫ b₁₂))
          (pasted.whiskerRight (pullbackComp b₀₁ b₁₂).inv)).whiskerTop
            (pushforwardComp a₀₁ a₁₂).inv := by
    rw [conjugateEquiv_mateEquiv_vcomp, pullbackComp_forward_mate]
  have mate :
      mateEquiv (A (a₀₁ ≫ a₁₂)) (A (b₀₁ ≫ b₁₂))
          ((pasted.whiskerRight (pullbackComp b₀₁ b₁₂).inv).whiskerLeft
            (pullbackComp a₀₁ a₁₂).hom) =
        (pushforwardSquare (a₀₁ ≫ a₁₂) v₀ v₂ (b₀₁ ≫ b₁₂) hOuter).hom := by
    rw [moveLeft, moveRight, pastedMate]
    simpa only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
      isoWhiskerRight_inv, isoWhiskerLeft_hom, Category.assoc] using
      (pushforwardSquare_pastePullback a₀₁ a₁₂ v₀ v₁ v₂
        b₀₁ b₁₂ h₀₁ h₁₂ hOuter).symm
  apply (mateEquiv (A (a₀₁ ≫ a₁₂)) (A (b₀₁ ≫ b₁₂))).injective
  rw [pushPull, Equiv.apply_symm_apply]
  simpa only [pasted, TwoSquare.whiskerRight, TwoSquare.whiskerLeft,
    TwoSquare.vComp, isoWhiskerLeft_inv, isoWhiskerRight_hom,
    Category.assoc] using mate.symm

end RingedSpaces.Modules.BaseChange

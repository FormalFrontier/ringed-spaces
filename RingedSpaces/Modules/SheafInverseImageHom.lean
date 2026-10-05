/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import RingedSpaces.Modules.SheafInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Adjunction for inverse-image sheaves of modules

The actual sheafification and coefficient comparison produce a bundled Hom
equivalence natural in both variables. Its right adjoint pushes modules through
the actual forgotten commutative-ring sheaf pullback unit.

## References

* Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry* (21 October 2025
  draft), Exercise 7.2.D(b,e) (p. 205), with the temporary presheaf in §2.7.2
  (p. 93): the full sheafified inverse-image/forward-image adjunction motivates
  this result. The natural linear Hom equivalence and coefficient transport
  are project proofs using Mathlib's sheaf pullback and adjunction APIs.
-/

@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace

namespace RingedSpaces.Modules.SheafInverseImage

universe v

variable {X Y : TopCat.{v}} (f : X ⟶ Y)

/-- Source coefficient sheaf, considered as a sheaf of ordinary rings. -/
abbrev sourceRing (S : Y.Sheaf CommRingCat.{v}) := (sheafForget Y).obj S

/-- The actual forgotten inverse-image sheaf of commutative rings. -/
noncomputable abbrev targetRing (S : Y.Sheaf CommRingCat.{v}) :=
  (sheafForget X).obj ((TopCat.Sheaf.pullback CommRingCat.{v} f).obj S)

/-- Neighborhood-colimit coefficient presheaf before sheafification. -/
noncomputable abbrev pointwiseRing (S : Y.Sheaf CommRingCat.{v}) :=
  (Opens.map f).op.pointwiseLeftKanExtension (sourceRing S).obj

/-- Ring sheafification of the neighborhood-colimit presheaf. -/
noncomputable abbrev sheafifiedRing (S : Y.Sheaf CommRingCat.{v}) :=
  RingedSpaces.Modules.PresheafInverseImage.inverseImageSheafRing f (sourceRing S).obj

/-- Category structure on sheaves of modules over a fixed ring sheaf. -/
instance moduleSheafCategory (R : X.Sheaf RingCat.{v}) :
    Category (SheafOfModules.{v} R) := SheafOfModules.instCategory

/-- The actual ring comparison needed for the final scalar restriction. -/
noncomputable def ringIso (S : Y.Sheaf CommRingCat.{v}) :
    targetRing f S ≅ sheafifiedRing f S :=
  RingedSpaces.Modules.SheafInverseImage.comparison f S ≪≫
    (RingedSpaces.Modules.PresheafInverseImage.inverseImageSheafRingComparison f (sourceRing S)).symm

/-- The actual commutative-ring inverse-image unit, forgotten to ring sheaves. -/
noncomputable def actualUnit (S : Y.Sheaf CommRingCat.{v}) :
    sourceRing S ⟶ (TopCat.Sheaf.pushforward RingCat.{v} f).obj (targetRing f S) :=
  (sheafForget Y).map
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{v} f).unit.app S)

set_option maxHeartbeats 1000000 in
theorem ringUnit_full (S : Y.Sheaf CommRingCat.{v})
    (V : (Opens Y)ᵒᵖ) (r : (sourceRing S).obj.obj V) :
    (ringIso f S).hom.hom.app ((Opens.map f).op.obj V)
      ((actualUnit f S).hom.app V r) =
    (toSheafify (Opens.grothendieckTopology X) (pointwiseRing f S)).app
      ((Opens.map f).op.obj V)
      (((Opens.map f).op.pointwiseLeftKanExtensionUnit (sourceRing S).obj).app V r) := by
  have hc := RingedSpaces.Modules.SheafInverseImage.comparison_unit_app f S V
  have hd := RingedSpaces.Modules.SheafInverseImage.ringUnit_pointwise f (sourceRing S) V r
  change (RingedSpaces.Modules.PresheafInverseImage.inverseImageSheafRingComparison f (sourceRing S)).inv.hom.app
      ((Opens.map f).op.obj V)
      ((RingedSpaces.Modules.SheafInverseImage.comparison f S).hom.hom.app
        ((Opens.map f).op.obj V) ((actualUnit f S).hom.app V r)) = _
  have hc' : (RingedSpaces.Modules.SheafInverseImage.comparison f S).hom.hom.app
      ((Opens.map f).op.obj V) ((actualUnit f S).hom.app V r) =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{v} f).unit.app
        (sourceRing S)).hom.app V r := by
    convert congrArg (fun t => t r) hc using 1; rfl
  rw [hc']
  exact hd

set_option maxHeartbeats 1000000 in
/-- The complete ring-map identity, not merely an equality of underlying additive maps. -/
theorem ringUnit_iso (S : Y.Sheaf CommRingCat.{v}) :
    actualUnit f S ≫
      (TopCat.Sheaf.pushforward RingCat.{v} f).map (ringIso f S).hom =
    RingedSpaces.Modules.SheafInverseImage.pointwiseSheafUnit f RingCat.{v} (sourceRing S) := by
  apply (sheafToPresheaf (Opens.grothendieckTopology Y) RingCat.{v}).map_injective
  apply NatTrans.ext
  funext V
  apply RingCat.hom_ext
  apply RingHom.ext
  intro r
  exact ringUnit_full f S V r

/-- The reverse orientation identifies the actual unit with the pointwise unit
followed by the inverse scalar comparison. -/
theorem ringUnit_inverse (S : Y.Sheaf CommRingCat.{v}) :
    RingedSpaces.Modules.SheafInverseImage.pointwiseSheafUnit f RingCat.{v} (sourceRing S) ≫
      (TopCat.Sheaf.pushforward RingCat.{v} f).map (ringIso f S).inv =
    actualUnit f S := by
  exact ((TopCat.Sheaf.pushforward RingCat.{v} f).mapIso
    (ringIso f S)).comp_inv_eq.mpr (ringUnit_iso f S).symm

/-- The forward comparison followed by its inverse fixes sections. -/
theorem ringIso_hom_inv_apply (S : Y.Sheaf CommRingCat.{v})
    (V : (Opens X)ᵒᵖ) (b : (targetRing f S).obj.obj V) :
    (ringIso f S).inv.hom.app V ((ringIso f S).hom.hom.app V b) = b := by
  let e := (sheafToPresheaf (Opens.grothendieckTopology X) RingCat.{v}).mapIso
    (ringIso f S)
  have h := (e.app V).hom_inv_id
  change (ringIso f S).hom.hom.app V ≫ (ringIso f S).inv.hom.app V = 𝟙 _ at h
  simpa only [RingCat.comp_apply, RingCat.id_apply] using
    congrArg (fun map => map b) h

/-- The inverse comparison followed by its forward map fixes sections. -/
theorem ringIso_inv_hom_apply (S : Y.Sheaf CommRingCat.{v})
    (V : (Opens X)ᵒᵖ) (elem : (sheafifiedRing f S).obj.obj V) :
    (ringIso f S).hom.hom.app V ((ringIso f S).inv.hom.app V elem) = elem := by
  let e := (sheafToPresheaf (Opens.grothendieckTopology X) RingCat.{v}).mapIso
    (ringIso f S)
  have h := (e.app V).inv_hom_id
  change (ringIso f S).inv.hom.app V ≫ (ringIso f S).hom.hom.app V = 𝟙 _ at h
  simpa only [RingCat.comp_apply, RingCat.id_apply] using
    congrArg (fun map => map elem) h

/-- Transfer a module sheaf over the actual inverse-image ring to the
sheafified pointwise ring along the inverse of the genuine comparison. -/
noncomputable def targetTransport (S : Y.Sheaf CommRingCat.{v}) :
    SheafOfModules.{v} (targetRing f S) ⥤ SheafOfModules.{v} (sheafifiedRing f S) :=
  SheafOfModules.restrictScalars (ringIso f S).inv

/-- Scalar transport on a Hom: the additive section maps are unchanged. -/
noncomputable def transportForward (S : Y.Sheaf CommRingCat.{v})
    {H : SheafOfModules.{v} (sheafifiedRing f S)}
    {N : SheafOfModules.{v} (targetRing f S)}
    (g : (SheafOfModules.restrictScalars (ringIso f S).hom).obj H ⟶ N) :
    H ⟶ (targetTransport f S).obj N :=
  ⟨PresheafOfModules.homMk ((PresheafOfModules.toPresheaf (targetRing f S).obj).map g.val)
    (by
      intro V t m
      have hg := (g.val.app V).hom.map_smul ((ringIso f S).inv.hom.app V t) m
      change g.val.app V (t • m) = (ringIso f S).inv.hom.app V t • g.val.app V m
      calc
        _ = g.val.app V
            ((ringIso f S).hom.hom.app V ((ringIso f S).inv.hom.app V t) • m) := by
              rw [ringIso_inv_hom_apply f S V t]
        _ = _ := hg)⟩

/-- Inverse scalar transport on a Hom, retaining every section map and restriction. -/
noncomputable def transportBackward (S : Y.Sheaf CommRingCat.{v})
    {H : SheafOfModules.{v} (sheafifiedRing f S)}
    {N : SheafOfModules.{v} (targetRing f S)}
    (g : H ⟶ (targetTransport f S).obj N) :
    (SheafOfModules.restrictScalars (ringIso f S).hom).obj H ⟶ N :=
  ⟨PresheafOfModules.homMk ((PresheafOfModules.toPresheaf (sheafifiedRing f S).obj).map g.val)
    (by
      intro V b m
      have hg := (g.val.app V).hom.map_smul ((ringIso f S).hom.hom.app V b) m
      change g.val.app V (b • m) = b • (show N.val.obj V from g.val.app V m)
      have hg' : g.val.app V (b • m) =
          (ringIso f S).inv.hom.app V ((ringIso f S).hom.hom.app V b) •
            (show N.val.obj V from g.val.app V m) := by
        convert hg using 1; rfl
      simpa only [ringIso_hom_inv_apply] using hg')⟩

theorem transport_backward_forward (S : Y.Sheaf CommRingCat.{v})
    {H : SheafOfModules.{v} (sheafifiedRing f S)}
    {N : SheafOfModules.{v} (targetRing f S)}
    (g : (SheafOfModules.restrictScalars (ringIso f S).hom).obj H ⟶ N) :
    transportBackward f S (transportForward f S g) = g := by
  apply SheafOfModules.hom_ext
  apply (PresheafOfModules.toPresheaf _).map_injective
  rfl

theorem transport_forward_backward (S : Y.Sheaf CommRingCat.{v})
    {H : SheafOfModules.{v} (sheafifiedRing f S)}
    {N : SheafOfModules.{v} (targetRing f S)}
    (g : H ⟶ (targetTransport f S).obj N) :
    transportForward f S (transportBackward f S g) = g := by
  apply SheafOfModules.hom_ext
  apply (PresheafOfModules.toPresheaf _).map_injective
  rfl

/-- A full two-sided Hom equivalence across the nonidentity comparison. -/
noncomputable def transportHomEquiv (S : Y.Sheaf CommRingCat.{v})
    (H : SheafOfModules.{v} (sheafifiedRing f S))
    (N : SheafOfModules.{v} (targetRing f S)) :
    ((SheafOfModules.restrictScalars (ringIso f S).hom).obj H ⟶ N) ≃
      (H ⟶ (targetTransport f S).obj N) where
  toFun := transportForward f S
  invFun := transportBackward f S
  left_inv := transport_backward_forward f S
  right_inv := transport_forward_backward f S

theorem transport_naturality_left (S : Y.Sheaf CommRingCat.{v})
    {H H' : SheafOfModules.{v} (sheafifiedRing f S)}
    {N : SheafOfModules.{v} (targetRing f S)}
    (h : H' ⟶ H)
    (g : (SheafOfModules.restrictScalars (ringIso f S).hom).obj H ⟶ N) :
    transportForward f S
        ((SheafOfModules.restrictScalars (ringIso f S).hom).map h ≫ g) =
      h ≫ transportForward f S g := by
  apply SheafOfModules.hom_ext
  apply (PresheafOfModules.toPresheaf _).map_injective
  rfl

theorem transport_naturality_right (S : Y.Sheaf CommRingCat.{v})
    {H : SheafOfModules.{v} (sheafifiedRing f S)}
    {N N' : SheafOfModules.{v} (targetRing f S)}
    (g : (SheafOfModules.restrictScalars (ringIso f S).hom).obj H ⟶ N)
    (h : N ⟶ N') :
    transportForward f S (g ≫ h) =
      transportForward f S g ≫ (targetTransport f S).map h := by
  apply SheafOfModules.hom_ext
  apply (PresheafOfModules.toPresheaf _).map_injective
  rfl

/-- The actual native sheaf-module pushforward, not an abstract right adjoint. -/
noncomputable def pushforwardFunctor (S : Y.Sheaf CommRingCat.{v}) :
    SheafOfModules.{v} (targetRing f S) ⥤ SheafOfModules.{v} (sourceRing S) :=
  SheafOfModules.pushforward (F := Opens.map f) (actualUnit f S)

/-- The ring sheafification unit used for the presheaf adjunction. -/
noncomputable abbrev coefficientSheafUnit (S : Y.Sheaf CommRingCat.{v}) :=
  toSheafify (Opens.grothendieckTopology X) (pointwiseRing f S)

/-- The underlying presheaf of a target sheaf module. -/
noncomputable abbrev presheafTarget (S : Y.Sheaf CommRingCat.{v})
    (N : SheafOfModules.{v} (targetRing f S)) :=
  (PresheafOfModules.pushforward (F := Opens.map f)
    ((Opens.map f).op.pointwiseLeftKanExtensionUnit (sourceRing S).obj)).obj
      ((PresheafOfModules.restrictScalars (coefficientSheafUnit f S)).obj
        ((targetTransport f S).obj N).val)

theorem ringUnit_inverse_apply (S : Y.Sheaf CommRingCat.{v})
    (V : (Opens Y)ᵒᵖ) (r : (sourceRing S).obj.obj V) :
    (ringIso f S).inv.hom.app ((Opens.map f).op.obj V)
      ((coefficientSheafUnit f S).app ((Opens.map f).op.obj V)
        (((Opens.map f).op.pointwiseLeftKanExtensionUnit (sourceRing S).obj).app V r)) =
      (actualUnit f S).hom.app V r := by
  rw [← ringUnit_full f S V r]
  exact ringIso_hom_inv_apply f S ((Opens.map f).op.obj V)
    ((actualUnit f S).hom.app V r)

/-- Pushforward along the pointwise ring unit before sheafifying. -/
noncomputable abbrev nativePushedTarget (S : Y.Sheaf CommRingCat.{v})
    (N : SheafOfModules.{v} (targetRing f S)) :=
  ((pushforwardFunctor f S).obj N).val

/-- The coefficient comparison acts identically on every target section. -/
noncomputable def targetMap (S : Y.Sheaf CommRingCat.{v})
    (N : SheafOfModules.{v} (targetRing f S)) :
    presheafTarget f S N ⟶ nativePushedTarget f S N :=
  PresheafOfModules.homMk (𝟙 _) (by
    intro V r m
    change (ringIso f S).inv.hom.app ((Opens.map f).op.obj V)
        ((coefficientSheafUnit f S).app ((Opens.map f).op.obj V)
          (((Opens.map f).op.pointwiseLeftKanExtensionUnit (sourceRing S).obj).app V r)) •
        (show N.val.obj ((Opens.map f).op.obj V) from m) =
      (show (targetRing f S).obj.obj ((Opens.map f).op.obj V) from
        (actualUnit f S).hom.app V r) •
        (show N.val.obj ((Opens.map f).op.obj V) from m)
    rw [ringUnit_inverse_apply f S V r])

/-- The inverse identity-on-sections coefficient comparison. -/
noncomputable def targetMapInv (S : Y.Sheaf CommRingCat.{v})
    (N : SheafOfModules.{v} (targetRing f S)) :
    nativePushedTarget f S N ⟶ presheafTarget f S N :=
  PresheafOfModules.homMk (𝟙 _) (by
    intro V r m
    change (show (targetRing f S).obj.obj ((Opens.map f).op.obj V) from
        (actualUnit f S).hom.app V r) •
        (show N.val.obj ((Opens.map f).op.obj V) from m) =
      (ringIso f S).inv.hom.app ((Opens.map f).op.obj V)
        ((coefficientSheafUnit f S).app ((Opens.map f).op.obj V)
          (((Opens.map f).op.pointwiseLeftKanExtensionUnit (sourceRing S).obj).app V r)) •
        (show N.val.obj ((Opens.map f).op.obj V) from m)
    rw [ringUnit_inverse_apply f S V r])

/-- The actual target comparison is an isomorphism over all ring coefficients. -/
noncomputable def targetIso (S : Y.Sheaf CommRingCat.{v})
    (N : SheafOfModules.{v} (targetRing f S)) :
    presheafTarget f S N ≅ nativePushedTarget f S N where
  hom := targetMap f S N
  inv := targetMapInv f S N
  hom_inv_id := by
    apply (PresheafOfModules.toPresheaf _).map_injective
    rfl
  inv_hom_id := by
    apply (PresheafOfModules.toPresheaf _).map_injective
    rfl

/-- Equivalence on morphisms given by postcomposing with an isomorphism. -/
noncomputable def postcomposeIso {C : Type*} [Category C]
    {A B D : C} (e : B ≅ D) : (A ⟶ B) ≃ (A ⟶ D) where
  toFun g := g ≫ e.hom
  invFun g := g ≫ e.inv
  left_inv g := by simp
  right_inv g := by simp

/-- Actual bundled sheaf-module maps in both directions, by native sheafification,
neighborhood-colimit descent and a full scalar target comparison. -/
noncomputable def homEquiv (S : Y.Sheaf CommRingCat.{v})
    (M : SheafOfModules.{v} (sourceRing S))
    (N : SheafOfModules.{v} (targetRing f S)) :
    ((RingedSpaces.Modules.SheafInverseImage.moduleFunctor f S).obj M ⟶ N) ≃
      (M ⟶ (pushforwardFunctor f S).obj N) :=
  (transportHomEquiv f S
      ((PresheafOfModules.sheafification (coefficientSheafUnit f S)).obj
        ((RingedSpaces.Modules.PresheafInverseImage.inverseImageFunctor f (sourceRing S).obj).obj M.val)) N).trans
    ((PresheafOfModules.sheafificationHomEquiv (coefficientSheafUnit f S)).trans
      ((RingedSpaces.Modules.PresheafInverseImage.homEquiv f (sourceRing S).obj M.val
        ((PresheafOfModules.restrictScalars (coefficientSheafUnit f S)).obj
          ((targetTransport f S).obj N).val)).trans
        ((postcomposeIso (targetIso f S N)).trans
          ((SheafOfModules.fullyFaithfulForget (sourceRing S)).homEquiv
            (X := M) (Y := (pushforwardFunctor f S).obj N)).symm)))

/-- The full forward transpose on sections is the existing additive module unit
followed by the actual target morphism on the inverse-image open. -/
theorem forward_apply (S : Y.Sheaf CommRingCat.{v})
    {M : SheafOfModules.{v} (sourceRing S)}
    {N : SheafOfModules.{v} (targetRing f S)}
    (g : (RingedSpaces.Modules.SheafInverseImage.moduleFunctor f S).obj M ⟶ N)
    (V : (Opens Y)ᵒᵖ) (m : M.val.obj V) :
    ((homEquiv f S M N g).val.app V) m =
      g.val.app ((Opens.map f).op.obj V)
        ((RingedSpaces.Modules.SheafInverseImage.moduleUnit f S M).hom.app V m) := by
  rw [RingedSpaces.Modules.SheafInverseImage.moduleUnit_pointwise f S M V m]
  rfl

theorem homEquiv_naturality_right (S : Y.Sheaf CommRingCat.{v})
    {M : SheafOfModules.{v} (sourceRing S)}
    {N N' : SheafOfModules.{v} (targetRing f S)}
    (g : (RingedSpaces.Modules.SheafInverseImage.moduleFunctor f S).obj M ⟶ N)
    (h : N ⟶ N') :
    homEquiv f S M N' (g ≫ h) =
      homEquiv f S M N g ≫ (pushforwardFunctor f S).map h := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  rw [forward_apply f S (g ≫ h) V m]
  change h.val.app ((Opens.map f).op.obj V)
      (g.val.app ((Opens.map f).op.obj V)
        ((RingedSpaces.Modules.SheafInverseImage.moduleUnit f S M).hom.app V m)) =
    h.val.app ((Opens.map f).op.obj V) ((homEquiv f S M N g).val.app V m)
  rw [forward_apply f S g V m]

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
theorem additiveUnit_naturality (S : Y.Sheaf CommRingCat.{v})
    {M M' : SheafOfModules.{v} (sourceRing S)} (h : M ⟶ M') :
    (SheafOfModules.toSheaf (sourceRing S)).map h ≫
      RingedSpaces.Modules.SheafInverseImage.moduleUnit f S M' =
    RingedSpaces.Modules.SheafInverseImage.moduleUnit f S M ≫
      (TopCat.Sheaf.pushforward AddCommGrpCat.{v} f).map
        ((SheafOfModules.toSheaf (targetRing f S)).map
          ((RingedSpaces.Modules.SheafInverseImage.moduleFunctor f S).map h)) := by
  let sourceForget := SheafOfModules.toSheaf (sourceRing S)
  let targetForget := SheafOfModules.toSheaf (targetRing f S)
  let inverseImage := RingedSpaces.Modules.SheafInverseImage.moduleFunctor f S
  let additivePullback := TopCat.Sheaf.pullback AddCommGrpCat.{v} f
  let additivePushforward := TopCat.Sheaf.pushforward AddCommGrpCat.{v} f
  let additiveAdj := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{v} f
  let additiveComparison := RingedSpaces.Modules.SheafInverseImage.moduleUnderlyingNatIso f S
  have hunit := additiveAdj.unit.naturality (sourceForget.map h)
  have hcomparison := additiveComparison.inv.naturality h
  simp only [Functor.id_map, Functor.comp_map] at hunit hcomparison
  change sourceForget.map h ≫
      (additiveAdj.unit.app (sourceForget.obj M') ≫
        additivePushforward.map (additiveComparison.inv.app M')) =
    (additiveAdj.unit.app (sourceForget.obj M) ≫
      additivePushforward.map (additiveComparison.inv.app M)) ≫
        additivePushforward.map (targetForget.map (inverseImage.map h))
  calc
    _ = (additiveAdj.unit.app (sourceForget.obj M) ≫
          additivePushforward.map (additivePullback.map (sourceForget.map h))) ≫
            additivePushforward.map (additiveComparison.inv.app M') := by
          rw [← Category.assoc, hunit]
    _ = additiveAdj.unit.app (sourceForget.obj M) ≫
          additivePushforward.map
            (additivePullback.map (sourceForget.map h) ≫
              additiveComparison.inv.app M') := by
          rw [Category.assoc, Functor.map_comp]
    _ = additiveAdj.unit.app (sourceForget.obj M) ≫
          additivePushforward.map
            (additiveComparison.inv.app M ≫ targetForget.map (inverseImage.map h)) := by
          congr 1
          exact congrArg (fun t => additivePushforward.map t) hcomparison
    _ = _ := by rw [Functor.map_comp, Category.assoc]

theorem additiveUnit_naturality_apply (S : Y.Sheaf CommRingCat.{v})
    {M M' : SheafOfModules.{v} (sourceRing S)} (h : M ⟶ M')
    (V : (Opens Y)ᵒᵖ) (m : M.val.obj V) :
    (RingedSpaces.Modules.SheafInverseImage.moduleUnit f S M').hom.app V (h.val.app V m) =
      ((RingedSpaces.Modules.SheafInverseImage.moduleFunctor f S).map h).val.app
        ((Opens.map f).op.obj V)
        ((RingedSpaces.Modules.SheafInverseImage.moduleUnit f S M).hom.app V m) := by
  have hnat := additiveUnit_naturality f S h
  have hv := NatTrans.congr_app (congrArg (fun t => t.hom) hnat) V
  convert congrArg (fun t => t m) hv using 1; rfl

theorem homEquiv_naturality_left (S : Y.Sheaf CommRingCat.{v})
    {M M' : SheafOfModules.{v} (sourceRing S)}
    {N : SheafOfModules.{v} (targetRing f S)}
    (h : M' ⟶ M)
    (g : (RingedSpaces.Modules.SheafInverseImage.moduleFunctor f S).obj M ⟶ N) :
    homEquiv f S M' N
        ((RingedSpaces.Modules.SheafInverseImage.moduleFunctor f S).map h ≫ g) =
      h ≫ homEquiv f S M N g := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  rw [forward_apply f S
    ((RingedSpaces.Modules.SheafInverseImage.moduleFunctor f S).map h ≫ g) V m]
  change g.val.app ((Opens.map f).op.obj V)
      (((RingedSpaces.Modules.SheafInverseImage.moduleFunctor f S).map h).val.app
        ((Opens.map f).op.obj V)
        ((RingedSpaces.Modules.SheafInverseImage.moduleUnit f S M').hom.app V m)) =
    (homEquiv f S M N g).val.app V (h.val.app V m)
  rw [← additiveUnit_naturality_apply f S h V m]
  exact (forward_apply f S g V (h.val.app V m)).symm

/-- The actual forward bundled map. -/
noncomputable def forward (S : Y.Sheaf CommRingCat.{v})
    {M : SheafOfModules.{v} (sourceRing S)}
    {N : SheafOfModules.{v} (targetRing f S)}
    (g : (RingedSpaces.Modules.SheafInverseImage.moduleFunctor f S).obj M ⟶ N) :
    M ⟶ (pushforwardFunctor f S).obj N :=
  homEquiv f S M N g

/-- The actual backward bundled map, not an assumed inverse scalar law. -/
noncomputable def backward (S : Y.Sheaf CommRingCat.{v})
    {M : SheafOfModules.{v} (sourceRing S)}
    {N : SheafOfModules.{v} (targetRing f S)}
    (g : M ⟶ (pushforwardFunctor f S).obj N) :
    (RingedSpaces.Modules.SheafInverseImage.moduleFunctor f S).obj M ⟶ N :=
  (homEquiv f S M N).symm g

theorem backward_forward (S : Y.Sheaf CommRingCat.{v})
    {M : SheafOfModules.{v} (sourceRing S)}
    {N : SheafOfModules.{v} (targetRing f S)}
    (g : (RingedSpaces.Modules.SheafInverseImage.moduleFunctor f S).obj M ⟶ N) :
    backward f S (forward f S g) = g :=
  Equiv.symm_apply_apply (homEquiv f S M N) g

theorem forward_backward (S : Y.Sheaf CommRingCat.{v})
    {M : SheafOfModules.{v} (sourceRing S)}
    {N : SheafOfModules.{v} (targetRing f S)}
    (g : M ⟶ (pushforwardFunctor f S).obj N) :
    forward f S (backward f S g) = g :=
  Equiv.apply_symm_apply (homEquiv f S M N) g

/-- Naturality turns the complete Hom equivalence into a genuine adjunction. -/
noncomputable def homEquivCore (S : Y.Sheaf CommRingCat.{v}) :
    Adjunction.CoreHomEquiv (RingedSpaces.Modules.SheafInverseImage.moduleFunctor f S)
      (pushforwardFunctor f S) where
  homEquiv := homEquiv f S
  homEquiv_naturality_left_symm := by
    intro M' M N h g
    apply (homEquiv f S M' N).injective
    change forward f S (backward f S (h ≫ g)) =
      forward f S ((RingedSpaces.Modules.SheafInverseImage.moduleFunctor f S).map h ≫
        backward f S g)
    rw [forward_backward f S (h ≫ g)]
    change h ≫ g = homEquiv f S M' N
      ((RingedSpaces.Modules.SheafInverseImage.moduleFunctor f S).map h ≫ backward f S g)
    rw [homEquiv_naturality_left f S h]
    exact (congrArg (fun t => h ≫ t) (forward_backward f S g)).symm
  homEquiv_naturality_right := by
    intro M N N' g h
    exact homEquiv_naturality_right f S g h

/-- Existing inverse-image sheaf-module functor is left adjoint to native
pushforward along the forgotten actual commutative-ring inverse-image unit. -/
noncomputable def adjunction (S : Y.Sheaf CommRingCat.{v}) :
    RingedSpaces.Modules.SheafInverseImage.moduleFunctor f S ⊣ pushforwardFunctor f S :=
  Adjunction.mkOfHomEquiv (homEquivCore f S)

theorem unit_app_eq (S : Y.Sheaf CommRingCat.{v})
    (M : SheafOfModules.{v} (sourceRing S)) :
    (adjunction f S).unit.app M =
      forward f S (𝟙 ((RingedSpaces.Modules.SheafInverseImage.moduleFunctor f S).obj M)) := rfl

theorem counit_app_eq (S : Y.Sheaf CommRingCat.{v})
    (N : SheafOfModules.{v} (targetRing f S)) :
    (adjunction f S).counit.app N =
      backward f S (𝟙 ((pushforwardFunctor f S).obj N)) := rfl

theorem left_triangle (S : Y.Sheaf CommRingCat.{v})
    (M : SheafOfModules.{v} (sourceRing S)) :
    (RingedSpaces.Modules.SheafInverseImage.moduleFunctor f S).map ((adjunction f S).unit.app M) ≫
      (adjunction f S).counit.app
        ((RingedSpaces.Modules.SheafInverseImage.moduleFunctor f S).obj M) =
      𝟙 ((RingedSpaces.Modules.SheafInverseImage.moduleFunctor f S).obj M) :=
  (adjunction f S).left_triangle_components M

theorem right_triangle (S : Y.Sheaf CommRingCat.{v})
    (N : SheafOfModules.{v} (targetRing f S)) :
    (adjunction f S).unit.app ((pushforwardFunctor f S).obj N) ≫
      (pushforwardFunctor f S).map ((adjunction f S).counit.app N) =
      𝟙 ((pushforwardFunctor f S).obj N) :=
  (adjunction f S).right_triangle_components N

/-- Equality of entire underlying sheaf maps, not only generator values. -/
theorem forward_underlying (S : Y.Sheaf CommRingCat.{v})
    {M : SheafOfModules.{v} (sourceRing S)}
    {N : SheafOfModules.{v} (targetRing f S)}
    (g : (RingedSpaces.Modules.SheafInverseImage.moduleFunctor f S).obj M ⟶ N) :
    (SheafOfModules.toSheaf (sourceRing S)).map (forward f S g) =
      RingedSpaces.Modules.SheafInverseImage.moduleUnit f S M ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{v} f).map
          ((SheafOfModules.toSheaf (targetRing f S)).map g) := by
  apply (sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{v}).map_injective
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro m
  exact forward_apply f S g V m

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Ordinary additive sheaf adjunction transpose of the module map after
the existing coherence isomorphism, for the full underlying sheaf morphism. -/
theorem forward_underlying_additive (S : Y.Sheaf CommRingCat.{v})
    {M : SheafOfModules.{v} (sourceRing S)}
    {N : SheafOfModules.{v} (targetRing f S)}
    (g : (RingedSpaces.Modules.SheafInverseImage.moduleFunctor f S).obj M ⟶ N) :
    (SheafOfModules.toSheaf (sourceRing S)).map (forward f S g) =
      (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{v} f).homEquiv
        ((SheafOfModules.toSheaf (sourceRing S)).obj M)
        ((SheafOfModules.toSheaf (targetRing f S)).obj N)
        ((RingedSpaces.Modules.SheafInverseImage.moduleUnderlying f S M).inv ≫
          (SheafOfModules.toSheaf (targetRing f S)).map g) := by
  rw [forward_underlying f S g]
  calc
    _ = (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{v} f).unit.app
          ((SheafOfModules.toSheaf (sourceRing S)).obj M) ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{v} f).map
          ((RingedSpaces.Modules.SheafInverseImage.moduleUnderlying f S M).inv ≫
            (SheafOfModules.toSheaf (targetRing f S)).map g) := by
          simp only [RingedSpaces.Modules.SheafInverseImage.moduleUnit, Functor.map_comp,
            Category.assoc]
          rfl
    _ = _ := ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{v} f).homEquiv_unit
      ((SheafOfModules.toSheaf (sourceRing S)).obj M)
      ((SheafOfModules.toSheaf (targetRing f S)).obj N)
      ((RingedSpaces.Modules.SheafInverseImage.moduleUnderlying f S M).inv ≫
        (SheafOfModules.toSheaf (targetRing f S)).map g)).symm

set_option backward.isDefEq.respectTransparency false in
/-- The module adjunction unit forgets exactly to the existing additive unit. -/
theorem unit_underlying (S : Y.Sheaf CommRingCat.{v})
    (M : SheafOfModules.{v} (sourceRing S)) :
    (SheafOfModules.toSheaf (sourceRing S)).map ((adjunction f S).unit.app M) =
      RingedSpaces.Modules.SheafInverseImage.moduleUnit f S M := by
  rw [unit_app_eq f S M, forward_underlying f S]
  apply (sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{v}).map_injective
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro m
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The inverse additive transpose is forced by the genuine bundled inverse,
not assumed as a scalar-compatibility law. -/
theorem backward_underlying_additive (S : Y.Sheaf CommRingCat.{v})
    {M : SheafOfModules.{v} (sourceRing S)}
    {N : SheafOfModules.{v} (targetRing f S)}
    (g : M ⟶ (pushforwardFunctor f S).obj N) :
    (RingedSpaces.Modules.SheafInverseImage.moduleUnderlying f S M).inv ≫
      (SheafOfModules.toSheaf (targetRing f S)).map (backward f S g) =
    ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{v} f).homEquiv
      ((SheafOfModules.toSheaf (sourceRing S)).obj M)
      ((SheafOfModules.toSheaf (targetRing f S)).obj N)).symm
        ((SheafOfModules.toSheaf (sourceRing S)).map g) := by
  let additiveEquiv :=
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{v} f).homEquiv
      ((SheafOfModules.toSheaf (sourceRing S)).obj M)
      ((SheafOfModules.toSheaf (targetRing f S)).obj N)
  apply additiveEquiv.injective
  calc
    _ = (SheafOfModules.toSheaf (sourceRing S)).map
          (forward f S (backward f S g)) :=
        (forward_underlying_additive f S (backward f S g)).symm
    _ = (SheafOfModules.toSheaf (sourceRing S)).map g := by
          rw [forward_backward f S g]
    _ = additiveEquiv (additiveEquiv.symm
          ((SheafOfModules.toSheaf (sourceRing S)).map g)) :=
        (additiveEquiv.apply_symm_apply _).symm

end RingedSpaces.Modules.SheafInverseImage

#lint

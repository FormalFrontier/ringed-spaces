/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import RingedSpaces.FiniteRegularityFunctions

/-!
# Maps of finite-regularity scalar function spaces

A `C^r` map between charted spaces over the same normed field pulls scalar sections
backward along inverse images of opens. The induced sheaf morphism and its local
maps on germs give a morphism of locally ringed spaces. Smooth and continuous
function sheaves supply the comparison maps at the two regularity endpoints.

The regularity is relative to the chosen model-with-corners structures. No
chart-independence or equivalence with an intrinsic regularity condition is asserted.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold

universe u

namespace FiniteRegularityFunctions

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM] (IM : ModelWithCorners 𝕜 EM HM)
  {EN : Type*} [NormedAddCommGroup EN] [NormedSpace 𝕜 EN]
  {HN : Type*} [TopologicalSpace HN] (IN : ModelWithCorners 𝕜 EN HN)
  (M N : Type u) [TopologicalSpace M] [ChartedSpace HM M]
  [TopologicalSpace N] [ChartedSpace HN N]

/-- Pulling a finite-regularity scalar section back along a finite-regularity map
again gives a finite-regularity scalar function on the inverse-image open. -/
theorem section_comp_contMDiff (r : ℕ) (f : M → N)
    (hf : ContMDiff IM IN (r : ℕ∞ω) f) (U : Opens N)
    (s : (sheaf IN N r).presheaf.obj (op U)) :
    ContMDiff IM 𝓘(𝕜) (r : ℕ∞ω)
      (fun point : ContinuousFunctions.inverseImage M N f hf.continuous U =>
        s ⟨f point.1, point.2⟩) := by
  have hlift : ContMDiff IM IN (r : ℕ∞ω)
      (fun point : ContinuousFunctions.inverseImage M N f hf.continuous U =>
        (⟨f point.1, point.2⟩ : U)) := by
    intro point
    exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
      (fun point : ContinuousFunctions.inverseImage M N f hf.continuous U =>
        (⟨f point.1, point.2⟩ : U)) Set.univ point).mp
          ((hf.comp contMDiff_subtype_val) point)
  exact (section_contMDiff (IM := IN) (M := N) r U s).comp hlift

/-- The backward ring homomorphism on finite-regularity sections of an open set. -/
def precompose (r : ℕ) (f : M → N) (hf : ContMDiff IM IN (r : ℕ∞ω) f)
    (U : Opens N) :
    (sheaf IN N r).presheaf.obj (op U) →+*
      (sheaf IM M r).presheaf.obj
        (op (ContinuousFunctions.inverseImage M N f hf.continuous U)) where
  toFun s := ⟨fun point => s ⟨f point.1, point.2⟩,
    section_comp_contMDiff IM IN M N r f hf U s⟩
  map_one' := by apply section_ext; intro point; rfl
  map_mul' := by intros; apply section_ext; intro point; rfl
  map_zero' := by apply section_ext; intro point; rfl
  map_add' := by intros; apply section_ext; intro point; rfl

/-- Pullback of a section evaluates it at the image of the point. -/
@[simp] theorem precompose_apply (r : ℕ) (f : M → N)
    (hf : ContMDiff IM IN (r : ℕ∞ω) f) (U : Opens N)
    (s : (sheaf IN N r).presheaf.obj (op U))
    (point : ContinuousFunctions.inverseImage M N f hf.continuous U) :
    precompose IM IN M N r f hf U s point = s ⟨f point.1, point.2⟩ := by
  rfl

/-- Backward precomposition commutes with restriction of a section. -/
theorem precompose_restrict (r : ℕ) (f : M → N)
    (hf : ContMDiff IM IN (r : ℕ∞ω) f) {U V : Opens N} (h : U ≤ V)
    (s : (sheaf IN N r).presheaf.obj (op V)) :
    precompose IM IN M N r f hf U (restrict (IM := IN) (M := N) r h s) =
      restrict (IM := IM) (M := M) r
        (show ContinuousFunctions.inverseImage M N f hf.continuous U ≤
          ContinuousFunctions.inverseImage M N f hf.continuous V from
            fun _ hx => h hx)
        (precompose IM IN M N r f hf V s) := by
  apply section_ext (IM := IM) (M := M)
  intro point
  rfl

/-- Identity precomposition acts identically on section values. -/
theorem precompose_id_apply (r : ℕ) (U : Opens M)
    (s : (sheaf IM M r).presheaf.obj (op U))
    (point : ContinuousFunctions.inverseImage M M id
      (contMDiff_id : ContMDiff IM IM (r : ℕ∞ω) id).continuous U) :
    precompose IM IM M M r id contMDiff_id U s point = s ⟨point.1, point.2⟩ := by
  exact precompose_apply IM IM M M r id contMDiff_id U s point

section Composition

variable {EP : Type*} [NormedAddCommGroup EP] [NormedSpace 𝕜 EP]
  {HP : Type*} [TopologicalSpace HP] (IP : ModelWithCorners 𝕜 EP HP)
  (P : Type u) [TopologicalSpace P] [ChartedSpace HP P]

/-- Two successive backward precompositions agree with precomposition by the composite
at every point of their inverse-image open. -/
theorem precompose_comp_apply (r : ℕ) (f : M → N) (g : N → P)
    (hf : ContMDiff IM IN (r : ℕ∞ω) f)
    (hg : ContMDiff IN IP (r : ℕ∞ω) g) (U : Opens P)
    (s : (sheaf IP P r).presheaf.obj (op U))
    (point : ContinuousFunctions.inverseImage M N f hf.continuous
      (ContinuousFunctions.inverseImage N P g hg.continuous U)) :
    precompose IM IN M N r f hf
        (ContinuousFunctions.inverseImage N P g hg.continuous U)
        (precompose IN IP N P r g hg U s) point =
      precompose IM IP M P r (g ∘ f) (hg.comp hf) U s ⟨point.1, point.2⟩ := by
  rw [precompose_apply, precompose_apply, precompose_apply]
  exact congrArg (fun input : U => s input) (Subtype.ext rfl)

end Composition

/-- The morphism from finite-regularity scalar sections to their pushforward
along a finite-regularity map. -/
def sheafHom (r : ℕ) (f : M → N) (hf : ContMDiff IM IN (r : ℕ∞ω) f) :
    sheaf IN N r ⟶
      (TopCat.Sheaf.pushforward _ (TopCat.ofHom ⟨f, hf.continuous⟩)).obj
        (sheaf IM M r) where
  hom.app U := CommRingCat.ofHom (precompose IM IN M N r f hf U.unop)
  hom.naturality := by
    intro U V inclusion
    ext representative
    apply section_ext (IM := IM) (M := M)
    intro point
    rfl

/-- The sheaf map's component on an open set is backward precomposition. -/
theorem sheafHom_app (r : ℕ) (f : M → N)
    (hf : ContMDiff IM IN (r : ℕ∞ω) f) (U : Opens N) :
    (sheafHom IM IN M N r f hf).hom.app (op U) =
      CommRingCat.ofHom (precompose IM IN M N r f hf U) := by
  rfl

/-- The underlying presheafed-space morphism of finite-regularity scalar
function spaces. -/
def locallyRingedSpaceMapAux (r : ℕ) (f : M → N)
    (hf : ContMDiff IM IN (r : ℕ∞ω) f) :
    (locallyRingedSpace r IM M).toPresheafedSpace ⟶
      (locallyRingedSpace r IN N).toPresheafedSpace where
  base := TopCat.ofHom ⟨f, hf.continuous⟩
  c := (sheafHom IM IN M N r f hf).hom

/-- The backward map on stalks respects evaluation at the base point. -/
theorem stalkMap_evalHom_aux (r : ℕ) (f : M → N)
    (hf : ContMDiff IM IN (r : ℕ∞ω) f) (x : M) :
    (locallyRingedSpaceMapAux IM IN M N r f hf).stalkMap x ≫ evalHom IM M r x =
      evalHom IN N r (f x) := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hxU
  rw [PresheafedSpace.stalkMap_germ_assoc]
  ext representative
  exact (evalHom_germ (IM := IM) (M := M) r _ _ _ _).trans
    (evalHom_germ (IM := IN) (M := N) r _ _ _ _).symm

/-- A finite-regularity map induces a morphism of locally ringed spaces
by pulling back scalar sections. -/
def locallyRingedSpaceMap (r : ℕ) (f : M → N)
    (hf : ContMDiff IM IN (r : ℕ∞ω) f) :
    locallyRingedSpace r IM M ⟶ locallyRingedSpace r IN N where
  __ := locallyRingedSpaceMapAux IM IN M N r f hf
  prop x := by
    refine ⟨fun representative hsection => ?_⟩
    rw [isUnit_stalk_iff] at hsection
    rw [isUnit_stalk_iff]
    exact (congrArg (fun hom => hom representative)
      (stalkMap_evalHom_aux IM IN M N r f hf x)).symm ▸ hsection

/-- The underlying continuous map is the given finite-regularity map. -/
@[simp] theorem locallyRingedSpaceMap_base (r : ℕ) (f : M → N)
    (hf : ContMDiff IM IN (r : ℕ∞ω) f) :
    (locallyRingedSpaceMap IM IN M N r f hf).base =
      TopCat.ofHom ⟨f, hf.continuous⟩ := by
  rfl

/-- The map on germs pulls a representative back by precomposition. -/
@[simp] theorem stalkMap_germ (r : ℕ) (f : M → N)
    (hf : ContMDiff IM IN (r : ℕ∞ω) f) (U : Opens N)
    (x : M) (hx : f x ∈ U) (s : (sheaf IN N r).presheaf.obj (op U)) :
    (locallyRingedSpaceMap IM IN M N r f hf).stalkMap x
        ((sheaf IN N r).presheaf.germ U (f x) hx s) =
      (sheaf IM M r).presheaf.germ
        (ContinuousFunctions.inverseImage M N f hf.continuous U) x hx
        (precompose IM IN M N r f hf U s) := by
  exact LocallyRingedSpace.stalkMap_germ_apply
    (locallyRingedSpaceMap IM IN M N r f hf) U x hx s

/-- The backward stalk arrow commutes with evaluation. -/
@[reassoc (attr := simp)] theorem stalkMap_evalHom (r : ℕ) (f : M → N)
    (hf : ContMDiff IM IN (r : ℕ∞ω) f) (x : M) :
    (locallyRingedSpaceMap IM IN M N r f hf).stalkMap x ≫ evalHom IM M r x =
      evalHom IN N r (f x) := by
  exact stalkMap_evalHom_aux IM IN M N r f hf x

/-- The induced backward map on scalar-function germs is local. -/
theorem stalkMap_isLocalHom (r : ℕ) (f : M → N)
    (hf : ContMDiff IM IN (r : ℕ∞ω) f) (x : M) :
    IsLocalHom ((locallyRingedSpaceMap IM IN M N r f hf).stalkMap x).hom :=
  (locallyRingedSpaceMap IM IN M N r f hf).prop x

/-- Identity functions induce identity morphisms of entire locally ringed spaces. -/
theorem locallyRingedSpaceMap_id (r : ℕ) :
    locallyRingedSpaceMap IM IM M M r id contMDiff_id =
      𝟙 (locallyRingedSpace r IM M) := by
  apply LocallyRingedSpace.Hom.ext'
  refine PresheafedSpace.Hom.ext _ _ rfl ?_
  ext U representative
  rfl

section Composition

variable {EP : Type*} [NormedAddCommGroup EP] [NormedSpace 𝕜 EP]
  {HP : Type*} [TopologicalSpace HP] (IP : ModelWithCorners 𝕜 EP HP)
  (P : Type u) [TopologicalSpace P] [ChartedSpace HP P]

/-- Composition of finite-regularity maps induces composition of entire
locally ringed-space morphisms. -/
theorem locallyRingedSpaceMap_comp (r : ℕ) (f : M → N) (g : N → P)
    (hf : ContMDiff IM IN (r : ℕ∞ω) f)
    (hg : ContMDiff IN IP (r : ℕ∞ω) g) :
    locallyRingedSpaceMap IM IP M P r (g ∘ f) (hg.comp hf) =
      locallyRingedSpaceMap IM IN M N r f hf ≫
        locallyRingedSpaceMap IN IP N P r g hg := by
  apply LocallyRingedSpace.Hom.ext'
  refine PresheafedSpace.Hom.ext _ _ rfl ?_
  ext U representative
  rfl

end Composition

/-- Weakening smooth sections and then pulling back to finite order is the
same as pulling back smoothly and then weakening in the pushforward sheaf. -/
theorem smoothToFinite_naturality (r : ℕ) (f : M → N)
    (hf : ContMDiff IM IN ∞ f) :
    smoothToFinite (IM := IN) (M := N) r ≫
      sheafHom IM IN M N r f (hf.of_le (by simp)) =
      hf.smoothSheafCommRingHom _ _ f ≫
        (TopCat.Sheaf.pushforward _ (TopCat.ofHom ⟨f, hf.continuous⟩)).map
          (smoothToFinite (IM := IM) (M := M) r) := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro representative
  apply section_ext (IM := IM) (M := M)
  intro point
  rfl

/-- The zero-order precomposition map agrees with precomposition of continuous
functions after the natural zero-order sheaf isomorphisms. -/
theorem zeroSheafIso_naturality (f : M → N)
    (hf : ContMDiff IM IN (0 : ℕ∞ω) f) :
    (zeroSheafIso (IM := IN) (M := N)).hom ≫
      ContinuousFunctions.sheafHom M 𝕜 N f hf.continuous =
      sheafHom IM IN M N 0 f hf ≫
        (TopCat.Sheaf.pushforward _ (TopCat.ofHom ⟨f, hf.continuous⟩)).map
          (zeroSheafIso (IM := IM) (M := M)).hom := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro representative
  apply TopCat.ext
  intro point
  rfl

end FiniteRegularityFunctions

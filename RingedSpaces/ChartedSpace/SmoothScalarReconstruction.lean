/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Geometry.Manifold.Sheaf.LocallyRingedSpace
import Mathlib.Algebra.Order.Archimedean.Real.Hom

/-!
# Recovering smooth maps from scalar-preserving morphisms

The sheaf of smooth scalar functions already carried by a charted space determines
the smooth structure seen by its full morphisms. Preserving scalar constants on
global sections determines their pullbacks on every open and makes a full
morphism unique for a given base map. For an open finite-dimensional target,
this also recovers smoothness of the base map and the entire induced morphism.
For real scalars the constant-preservation condition is automatic, whereas it
remains an explicit hypothesis over general fields, including the complex field.

## Implementation notes

The scalar field and manifold carriers share a universe in the existing smooth
sheaf construction. The source model spaces need not share that universe. The smoothness
converse concerns open subspaces of finite-dimensional normed models; the
evaluation statement has no completeness or dimensionality requirements.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold

universe u v w x y z

namespace ChartedSpace

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
  {EM : Type v} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type w} [TopologicalSpace HM]
  (IM : ModelWithCorners 𝕜 EM HM)
  {M : Type z} [TopologicalSpace M] [ChartedSpace HM M]

variable {IM} {M : Type u} [TopologicalSpace M] [ChartedSpace HM M]
  {EN : Type x} [NormedAddCommGroup EN] [NormedSpace 𝕜 EN]
  {HN : Type y} [TopologicalSpace HN]
  {N : Type u} [TopologicalSpace N] [ChartedSpace HN N]
  (IN : ModelWithCorners 𝕜 EN HN)

/-- Restriction commutes with the canonical map of smooth scalar constants. -/
@[simp] theorem smoothScalarC_restrict {U V : Opens M} (h : V ≤ U) (a : 𝕜) :
    (smoothSheafCommRing IM 𝓘(𝕜) M 𝕜).presheaf.map (homOfLE h).op
      (ContMDiffMap.C (I := IM) (N := U) (A := 𝕜) (n := ∞) a) =
        ContMDiffMap.C (I := IM) (N := V) (A := 𝕜) (n := ∞) a := by
  apply Subtype.ext
  funext point
  rfl

/-- A morphism of canonical smooth scalar presheafed spaces preserves each scalar
constant on global sections. This condition does not require stalk locality. -/
def PreservesSmoothScalars
    (f : (locallyRingedSpace IM M).toPresheafedSpace ⟶
      (locallyRingedSpace IN N).toPresheafedSpace) : Prop :=
  ∀ (a : 𝕜) (point : (Opens.map f.base).obj (⊤ : Opens N)),
    (f.c.app (op (⊤ : Opens N))
      (ContMDiffMap.C (I := IN) (N := (⊤ : Opens N)) (A := 𝕜) (n := ∞) a)).1 point = a

/-- A scalar-preserving morphism takes each global scalar constant to the
same scalar at every point of its source. -/
theorem PreservesSmoothScalars.const_apply
    {f : (locallyRingedSpace IM M).toPresheafedSpace ⟶
      (locallyRingedSpace IN N).toPresheafedSpace}
    (hf : PreservesSmoothScalars IN f) (a : 𝕜)
    (point : (Opens.map f.base).obj (⊤ : Opens N)) :
    (f.c.app (op (⊤ : Opens N))
      (ContMDiffMap.C (I := IN) (N := (⊤ : Opens N)) (A := 𝕜) (n := ∞) a)).1 point = a :=
  hf a point

/-- Preserving global scalar constants is equivalent to preserving them on
every open set, by compatibility of sheaf morphisms with restrictions. -/
theorem preservesSmoothScalars_iff_allOpens
    (f : (locallyRingedSpace IM M).toPresheafedSpace ⟶
      (locallyRingedSpace IN N).toPresheafedSpace) :
    PreservesSmoothScalars IN f ↔
      ∀ (U : Opens N) (a : 𝕜),
        ∀ point : (Opens.map f.base).obj U,
          (f.c.app (op U)
            (ContMDiffMap.C (I := IN) (N := U) (A := 𝕜) (n := ∞) a)).1 point = a := by
  constructor
  · intro h U a point
    let inclusion : U ⟶ (⊤ : Opens N) := homOfLE le_top
    have natural := f.c.naturality inclusion.op
    have constantRes :
        (locallyRingedSpace IN N).presheaf.map inclusion.op
          (ContMDiffMap.C (I := IN) (N := (⊤ : Opens N)) (A := 𝕜) (n := ∞) a) =
            ContMDiffMap.C (I := IN) (N := U) (A := 𝕜) (n := ∞) a :=
      smoothScalarC_restrict (IM := IN) le_top a
    have restricted := congrArg (fun arrow =>
      arrow (ContMDiffMap.C (I := IN) (N := (⊤ : Opens N)) (A := 𝕜) (n := ∞) a)) natural
    change f.c.app (op U)
      ((locallyRingedSpace IN N).presheaf.map inclusion.op
        (ContMDiffMap.C (I := IN) (N := (⊤ : Opens N)) (A := 𝕜) (n := ∞) a)) =
      ((locallyRingedSpace IM M).presheaf.map
        ((Opens.map f.base).map inclusion).op)
        (f.c.app (op ⊤)
          (ContMDiffMap.C (I := IN) (N := (⊤ : Opens N)) (A := 𝕜) (n := ∞) a)) at restricted
    rw [constantRes] at restricted
    have atPoint := congrArg (fun representative => representative.1 point) restricted
    exact atPoint.trans (h a ⟨point.1, by trivial⟩)
  · intro h a point
    exact h ⊤ a point

/-- The smooth-induced full map preserves all scalar constants. -/
theorem preservesSmoothScalars_locallyRingedSpaceMap
    (map : M → N) (hmap : ContMDiff IM IN ∞ map) :
    PreservesSmoothScalars IN
      (locallyRingedSpaceMap map hmap).toHom := by
  intro a point
  rfl

/-- Scalar preservation is stable under identities. -/
theorem preservesSmoothScalars_id :
    PreservesSmoothScalars (M := M) (N := M) IM
      (𝟙 (locallyRingedSpace IM M).toPresheafedSpace) := by
  intro a point
  rfl

variable {EP : Type z} [NormedAddCommGroup EP] [NormedSpace 𝕜 EP]
  {HP : Type*} [TopologicalSpace HP]
  {P : Type u} [TopologicalSpace P] [ChartedSpace HP P]
  (IP : ModelWithCorners 𝕜 EP HP)

/-- Scalar-preserving morphisms are closed under composition. -/
theorem preservesSmoothScalars_comp
    {f : (locallyRingedSpace IM M).toPresheafedSpace ⟶
      (locallyRingedSpace IN N).toPresheafedSpace}
    {g : (locallyRingedSpace IN N).toPresheafedSpace ⟶
      (locallyRingedSpace IP P).toPresheafedSpace}
    (hf : PreservesSmoothScalars IN f) (hg : PreservesSmoothScalars IP g) :
    PreservesSmoothScalars IP (f ≫ g) := by
  apply (preservesSmoothScalars_iff_allOpens IP (f ≫ g)).2
  intro U a
  have hgU := (preservesSmoothScalars_iff_allOpens IP g).1 hg U a
  have hfU := (preservesSmoothScalars_iff_allOpens IN f).1 hf
    ((Opens.map g.base).obj U) a
  intro point
  change (f.c.app (op ((Opens.map g.base).obj U))
    (g.c.app (op U)
      (ContMDiffMap.C (I := IP) (N := U) (A := 𝕜) (n := ∞) a))).1 point = a
  let : ChartedSpace HN (↑(locallyRingedSpace IN N).toPresheafedSpace) :=
    (inferInstance : ChartedSpace HN N)
  have hconst : g.c.app (op U)
      (ContMDiffMap.C (I := IP) (N := U) (A := 𝕜) (n := ∞) a) =
      (ContMDiffMap.C (I := IN) (N := (Opens.map g.base).obj U)
        (A := 𝕜) (n := ∞) a :
        (smoothSheafCommRing IN 𝓘(𝕜) N 𝕜).presheaf.obj
          (op ((Opens.map g.base).obj U))) := by
    apply Subtype.ext
    funext p
    exact hgU p
  rw [hconst]
  exact hfU point

/-- Every morphism of canonical real smooth scalar presheaves preserves real
constants, since every ring endomorphism of `ℝ` is the identity. -/
theorem preservesSmoothScalars_real
    {ER : Type v} [NormedAddCommGroup ER] [NormedSpace ℝ ER]
    {HR : Type w} [TopologicalSpace HR] (IR : ModelWithCorners ℝ ER HR)
    {FR : Type x} [NormedAddCommGroup FR] [NormedSpace ℝ FR]
    {KR : Type y} [TopologicalSpace KR] (JR : ModelWithCorners ℝ FR KR)
    {MR NR : Type} [TopologicalSpace MR] [ChartedSpace HR MR]
    [TopologicalSpace NR] [ChartedSpace KR NR]
    (f : (locallyRingedSpace IR MR).toPresheafedSpace ⟶
      (locallyRingedSpace JR NR).toPresheafedSpace) :
    PreservesSmoothScalars JR f := by
  intro a point
  let : ChartedSpace HR (↑(locallyRingedSpace IR MR).toPresheafedSpace) :=
    (inferInstance : ChartedSpace HR MR)
  let scalarHom : ℝ →+* ℝ :=
    (ContMDiffMap.evalRingHom (I := IR) (I' := 𝓘(ℝ)) (n := ∞) point).comp
      ((f.c.app (op (⊤ : Opens NR))).hom.comp
        (ContMDiffMap.C (I := JR) (N := (⊤ : Opens NR)) (A := ℝ) (n := ∞)))
  change scalarHom a = a
  exact Real.ringHom_apply scalarHom a

/-- Pulling back a smooth scalar section along a scalar-preserving full
presheafed-space morphism is ordinary precomposition at each point. -/
theorem PreservesSmoothScalars.apply
    {f : (locallyRingedSpace IM M).toPresheafedSpace ⟶
      (locallyRingedSpace IN N).toPresheafedSpace}
    (hf : PreservesSmoothScalars IN f) (U : Opens N)
    (representative : (smoothSheafCommRing IN 𝓘(𝕜) N 𝕜).presheaf.obj (op U))
    (point : (Opens.map f.base).obj U) :
    (f.c.app (op U) representative :
      (smoothSheafCommRing IM 𝓘(𝕜) M 𝕜).presheaf.obj
        (op ((Opens.map f.base).obj U))).1 point =
        representative ⟨f.base point.1, point.2⟩ := by
  let value : 𝕜 := (f.c.app (op U) representative).1 point
  by_contra hvalue
  have hyU : f.base point.1 ∈ U := point.2
  let constant : (smoothSheafCommRing IN 𝓘(𝕜) N 𝕜).presheaf.obj (op U) :=
    ContMDiffMap.C (I := IN) (N := U) (A := 𝕜) (n := ∞) value
  let difference : (smoothSheafCommRing IN 𝓘(𝕜) N 𝕜).presheaf.obj (op U) :=
    representative - constant
  have htarget : difference ⟨f.base point.1, hyU⟩ ≠ 0 := by
    change representative ⟨f.base point.1, hyU⟩ - value ≠ 0
    exact sub_ne_zero.mpr (Ne.symm hvalue)
  have hunit : IsUnit ((locallyRingedSpace IN N).presheaf.germ U
      (f.base point.1) hyU difference) := by
    apply (smoothSheafCommRing.isUnit_stalk_iff IN _).2
    change smoothSheafCommRing.eval IN 𝓘(𝕜) N 𝕜 (f.base point.1)
      ((smoothSheafCommRing IN 𝓘(𝕜) N 𝕜).presheaf.germ U
        (f.base point.1) hyU difference) ≠ 0
    rw [smoothSheafCommRing.eval_germ]
    exact htarget
  have hsource : (f.c.app (op U) difference).1 point = 0 := by
    dsimp [difference]
    rw [map_sub]
    change value - (f.c.app (op U) constant).1 point = 0
    have hconstant : (f.c.app (op U) constant).1 point = value :=
      (preservesSmoothScalars_iff_allOpens IN f).1 hf U value point
    rw [hconstant]
    exact sub_self value
  have hzero : smoothSheafCommRing.eval IM 𝓘(𝕜) M 𝕜 point.1
      (f.stalkMap point.1 ((locallyRingedSpace IN N).presheaf.germ U
        (f.base point.1) hyU difference)) = 0 := by
    have hgerm : f.stalkMap point.1 ((locallyRingedSpace IN N).presheaf.germ U
        (f.base point.1) hyU difference) =
        (smoothSheafCommRing IM 𝓘(𝕜) M 𝕜).presheaf.germ
          ((Opens.map f.base).obj U) point.1 point.2 (f.c.app (op U) difference) :=
      PresheafedSpace.stalkMap_germ_apply f U point.1 hyU difference
    rw [hgerm, smoothSheafCommRing.eval_germ]
    exact hsource
  have hnonzero := (smoothSheafCommRing.isUnit_stalk_iff IM
    (f.stalkMap point.1 ((locallyRingedSpace IN N).presheaf.germ U
      (f.base point.1) hyU difference))).1
      (IsUnit.map (f.stalkMap point.1).hom hunit)
  exact hnonzero (by simpa only [RingHom.mem_ker] using hzero)

private theorem presheafedSpaceHom_c_heq
    {X Y : PresheafedSpace CommRingCat.{u}}
    {f g : X ⟶ Y} (h : f = g) : HEq f.c g.c := by
  cases h
  rfl

/-- Two scalar-preserving full morphisms with the same base map agree on every
smooth scalar section and hence are equal, for any canonical charted target. -/
theorem PreservesSmoothScalars.eq_of_base_eq
    {f g : (locallyRingedSpace IM M).toPresheafedSpace ⟶
      (locallyRingedSpace IN N).toPresheafedSpace}
    (hf : PreservesSmoothScalars IN f) (hg : PreservesSmoothScalars IN g)
    (hbase : f.base = g.base) : f = g := by
  rcases f with ⟨fbase, fc⟩
  rcases g with ⟨gbase, gc⟩
  dsimp at hbase
  cases hbase
  apply PresheafedSpace.Hom.ext ⟨fbase, fc⟩ ⟨fbase, gc⟩ rfl
  dsimp
  erw [Functor.whiskerRight_id', Category.comp_id]
  apply NatTrans.ext
  funext U
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro representative
  apply Subtype.ext
  funext point
  exact (hf.apply IN U.unop representative point).trans
    (hg.apply IN U.unop representative point).symm

set_option maxHeartbeats 5000000 in
-- Elaborating the full induced sheaf morphism for arbitrary charted spaces is expensive.

/-- A scalar-preserving morphism with an explicitly smooth base map is the
canonical full morphism for any charted target. -/
theorem PreservesSmoothScalars.eq_locallyRingedSpaceMap_of_contMDiff
    {f : (locallyRingedSpace IM M).toPresheafedSpace ⟶
      (locallyRingedSpace IN N).toPresheafedSpace}
    (hf : PreservesSmoothScalars IN f)
    (hbase : ContMDiff (M := M) (M' := N) IM IN ∞ (f.base : M → N)) :
    f = (locallyRingedSpaceMap (M := M) (N := N) (f.base : M → N) hbase).toHom := by
  let g : (locallyRingedSpace IM M).toPresheafedSpace ⟶
      (locallyRingedSpace IN N).toPresheafedSpace :=
    (locallyRingedSpaceMap (M := M) (N := N) (f.base : M → N) hbase).toHom
  have hg : PreservesSmoothScalars IN g :=
    preservesSmoothScalars_locallyRingedSpaceMap (M := M) (N := N) (IM := IM) (IN := IN)
      (f.base : M → N) hbase
  have hmaps : f.base = g.base := by
    apply TopCat.ext
    intro point
    rfl
  exact hf.eq_of_base_eq IN hg hmaps

/-- Equality with an induced morphism includes the entire sheaf component. -/
theorem PreservesSmoothScalars.eq_locallyRingedSpaceMap_c_of_contMDiff
    {f : (locallyRingedSpace IM M).toPresheafedSpace ⟶
      (locallyRingedSpace IN N).toPresheafedSpace}
    (hf : PreservesSmoothScalars IN f)
    (hbase : ContMDiff (M := M) (M' := N) IM IN ∞ (f.base : M → N)) :
    HEq f.c (locallyRingedSpaceMap (M := M) (N := N)
      (f.base : M → N) hbase).toHom.c :=
  presheafedSpaceHom_c_heq (hf.eq_locallyRingedSpaceMap_of_contMDiff IN hbase)

variable {F : Type u} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜]

/-- A scalar-preserving morphism into an open finite-dimensional model has a
smooth base map, without a finite-dimensionality assumption on its source. -/
theorem PreservesSmoothScalars.contMDiff_base {V : Opens F}
    {f : (locallyRingedSpace IM M).toPresheafedSpace ⟶
      (locallyRingedSpace 𝓘(𝕜, F) V).toPresheafedSpace}
    (hf : PreservesSmoothScalars 𝓘(𝕜, F) f) :
    ContMDiff (M := M) (M' := V) IM 𝓘(𝕜, F) ∞ (f.base : M → V) := by
  let : ChartedSpace HM (↑(locallyRingedSpace IM M).toPresheafedSpace) :=
    (inferInstance : ChartedSpace HM M)
  let coordinates : F ≃L[𝕜] (Fin (Module.finrank 𝕜 F) → 𝕜) :=
    (Module.finBasis 𝕜 F).equivFun.toContinuousLinearEquiv
  let coordinateSection (i : Fin (Module.finrank 𝕜 F)) :
      (smoothSheafCommRing 𝓘(𝕜, F) 𝓘(𝕜) V 𝕜).presheaf.obj (op ⊤) :=
    ⟨fun point => coordinates point.1 i, by
      let projection : (Fin (Module.finrank 𝕜 F) → 𝕜) →L[𝕜] 𝕜 :=
        ContinuousLinearMap.proj i
      have hcoordinate : ContMDiff 𝓘(𝕜, F) 𝓘(𝕜) ∞
          (fun point : (⊤ : Opens V) => coordinates point.1.1 i) := by
        have hsmooth : ContMDiff 𝓘(𝕜, F) 𝓘(𝕜) ∞
            ((projection ∘ coordinates.toContinuousLinearMap) ∘
              (Subtype.val : V → F) ∘
                (Subtype.val : (⊤ : Opens V) → V)) :=
          (projection.contMDiff.comp coordinates.toContinuousLinearMap.contMDiff).comp
            ((contMDiff_subtype_val (I := 𝓘(𝕜, F)) (U := V)).comp
              (contMDiff_subtype_val (I := 𝓘(𝕜, F)) (U := (⊤ : Opens V))))
        convert hsmooth using 1
        funext point
        rfl
      exact hcoordinate⟩
  have hcomponent (i : Fin (Module.finrank 𝕜 F)) :
      ContMDiff IM 𝓘(𝕜) ∞ (fun point : M => coordinates (f.base point).1 i) := by
    intro point
    let preimage : Opens M := (Opens.map f.base).obj (⊤ : Opens V)
    have hlocal : ContMDiffAt IM 𝓘(𝕜) ∞
        (fun source : preimage => coordinates (f.base source.1).1 i)
          ⟨point, by trivial⟩ := by
      have hfunctions : (fun source : preimage => coordinates (f.base source.1).1 i) =
          (f.c.app (op (⊤ : Opens V)) (coordinateSection i)).1 := by
        funext source
        exact (hf.apply 𝓘(𝕜, F) ⊤ (coordinateSection i) source).symm
      rw [hfunctions]
      exact (f.c.app (op ⊤) (coordinateSection i)).2 ⟨point, by trivial⟩
    exact (contMDiffAt_subtype_iff (I := IM) (I' := 𝓘(𝕜))
      (f := fun source : M => coordinates (f.base source).1 i)
      (U := preimage) (x := ⟨point, by trivial⟩)).1 hlocal
  have hall : ContMDiff IM 𝓘(𝕜, Fin (Module.finrank 𝕜 F) → 𝕜) ∞
      (fun point : M => coordinates (f.base point).1) :=
    contMDiff_pi_space.2 hcomponent
  have hvector : ContMDiff IM 𝓘(𝕜, F) ∞
      (fun point : M => (f.base point).1) := by
    have h := coordinates.symm.toContinuousLinearMap.contMDiff.comp hall
    convert h using 1
    funext point
    change (f.base point).1 = coordinates.symm (coordinates (f.base point).1)
    exact (coordinates.symm_apply_apply _).symm
  exact (ContMDiff.subtypeVal_comp_iff V (f.base : M → V)).1 hvector

/-- A scalar-preserving morphism into an open finite-dimensional model is
the full presheafed-space morphism induced by its smooth base map. -/
theorem PreservesSmoothScalars.eq_locallyRingedSpaceMap {V : Opens F}
    {f : (locallyRingedSpace IM M).toPresheafedSpace ⟶
      (locallyRingedSpace 𝓘(𝕜, F) V).toPresheafedSpace}
    (hf : PreservesSmoothScalars 𝓘(𝕜, F) f) :
    f = (locallyRingedSpaceMap (M := M) (N := V)
      (f.base : M → V) hf.contMDiff_base).toHom :=
  hf.eq_locallyRingedSpaceMap_of_contMDiff 𝓘(𝕜, F) hf.contMDiff_base

/-- Recovery includes equality of the entire sheaf component on every open,
not merely equality of the underlying continuous maps. -/
theorem PreservesSmoothScalars.eq_locallyRingedSpaceMap_c {V : Opens F}
    {f : (locallyRingedSpace IM M).toPresheafedSpace ⟶
      (locallyRingedSpace 𝓘(𝕜, F) V).toPresheafedSpace}
    (hf : PreservesSmoothScalars 𝓘(𝕜, F) f) :
    HEq f.c (locallyRingedSpaceMap (M := M) (N := V)
      (f.base : M → V) hf.contMDiff_base).toHom.c :=
  hf.eq_locallyRingedSpaceMap_c_of_contMDiff 𝓘(𝕜, F) hf.contMDiff_base

/-- For locally ringed-space morphisms, scalar preservation recovers the full
locally ringed-space arrow, not just its presheafed-space projection. -/
theorem PreservesSmoothScalars.eq_locallyRingedSpaceMap_of_locallyRingedSpace
    {V : Opens F} {f : locallyRingedSpace IM M ⟶ locallyRingedSpace 𝓘(𝕜, F) V}
    (hf : PreservesSmoothScalars 𝓘(𝕜, F) f.toHom) :
    f = locallyRingedSpaceMap (M := M) (N := V) (f.toHom.base : M → V)
      hf.contMDiff_base := by
  apply LocallyRingedSpace.Hom.ext'
  exact hf.eq_locallyRingedSpaceMap

/-- A morphism of canonical real smooth scalar presheaves into an open
finite-dimensional model has a smooth base without a separate scalar hypothesis. -/
theorem contMDiff_base_real
    {ER : Type v} [NormedAddCommGroup ER] [NormedSpace ℝ ER]
    {HR : Type w} [TopologicalSpace HR] {MR : Type}
    [TopologicalSpace MR] [ChartedSpace HR MR]
    (IR : ModelWithCorners ℝ ER HR)
    {FR : Type} [NormedAddCommGroup FR] [NormedSpace ℝ FR]
    [FiniteDimensional ℝ FR] {V : Opens FR}
    (f : (locallyRingedSpace IR MR).toPresheafedSpace ⟶
      (locallyRingedSpace 𝓘(ℝ, FR) V).toPresheafedSpace) :
    ContMDiff (M := MR) (M' := V) IR 𝓘(ℝ, FR) ∞ (f.base : MR → V) :=
  (preservesSmoothScalars_real IR 𝓘(ℝ, FR) f).contMDiff_base

/-- A full morphism of canonical real smooth scalar presheaves into an open
finite-dimensional model is induced by its smooth underlying map. -/
theorem eq_locallyRingedSpaceMap_real
    {ER : Type v} [NormedAddCommGroup ER] [NormedSpace ℝ ER]
    {HR : Type w} [TopologicalSpace HR] {MR : Type}
    [TopologicalSpace MR] [ChartedSpace HR MR]
    (IR : ModelWithCorners ℝ ER HR)
    {FR : Type} [NormedAddCommGroup FR] [NormedSpace ℝ FR]
    [FiniteDimensional ℝ FR] {V : Opens FR}
    (f : (locallyRingedSpace IR MR).toPresheafedSpace ⟶
      (locallyRingedSpace 𝓘(ℝ, FR) V).toPresheafedSpace) :
    f = (locallyRingedSpaceMap (M := MR) (N := V) (f.base : MR → V)
      (contMDiff_base_real IR f)).toHom :=
  (preservesSmoothScalars_real IR 𝓘(ℝ, FR) f).eq_locallyRingedSpaceMap

end ChartedSpace

/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import RingedSpaces.Complex.Holomorphic
public import RingedSpaces.ChartedSpace.SmoothLocalBall

/-!
# Holomorphic sections on open complex domains

On open subtypes of the complex line, holomorphic scalar functions are precisely
the sections of the existing complex-smooth scalar sheaf. These sections retain
the sheaf's restriction, germ and whole-morphism operations; no second sheaf
or locally ringed space is introduced.

The equivalences below apply to one complex variable, not arbitrary complex
manifolds or higher-dimensional complex model spaces. The scalar sheaf uses
the common-universe convention of `smoothSheafCommRing`.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold

namespace ComplexLine

private theorem contMDiff_iff_mdifferentiable_complex
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (f : M → F) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ, F) ∞ f ↔ MDifferentiable 𝓘(ℂ) 𝓘(ℂ, F) f := by
  constructor
  · intro hf
    exact hf.mdifferentiable (by norm_num)
  · intro hf point
    have hdiff : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ, F)
        (f ∘ (extChartAt 𝓘(ℂ) point).symm) (extChartAt 𝓘(ℂ) point).target :=
      hf.comp_mdifferentiableOn mdifferentiableOn_extChartAt_symm
    have hsmooth :=
      (contMDiffOn_iff_mdifferentiableOn_complex (isOpen_extChartAt_target point)).2 hdiff
    apply (contMDiffAt_iff_source_of_mem_source (mem_chart_source ℂ point)).2
    simpa only [ModelWithCorners.range_eq_univ, contMDiffWithinAt_univ] using
      hsmooth.contMDiffAt (extChartAt_target_mem_nhds point)

/-- A function on an open complex domain is complex-smooth exactly when it is
complex differentiable on its own domain, without requiring a global extension. -/
theorem smooth_iff_holomorphic_open (U : Opens ℂ) (f : U → ℂ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ f ↔ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f := by
  exact contMDiff_iff_mdifferentiable_complex f

/-- On a nested open subtype `V : Opens D`, holomorphicity is equivalent to
complex smoothness without requiring extension of `f` to the outer domain. -/
theorem smooth_iff_holomorphic (D : Opens ℂ) (V : Opens D) (f : V → ℂ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ f ↔ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f := by
  exact contMDiff_iff_mdifferentiable_complex f

/-- Regard a holomorphic representative as a section of the canonical
complex-smooth scalar sheaf on its open domain. -/
def ofHolomorphic (D : Opens ℂ) (V : Opens D) (f : V → ℂ)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    (smoothSheafCommRing 𝓘(ℂ) 𝓘(ℂ) D ℂ).presheaf.obj (op V) :=
  ⟨f, (smooth_iff_holomorphic D V f).2 hf⟩

/-- The canonical section retains the values of the holomorphic representative. -/
@[simp] theorem ofHolomorphic_apply (D : Opens ℂ) (V : Opens D) (f : V → ℂ)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (point : V) :
    ofHolomorphic D V f hf point = f point := rfl

/-- Evaluation of the canonical germ of a holomorphic representative returns
its value at the point. -/
@[simp] theorem ofHolomorphic_eval_germ (D : Opens ℂ) (V : Opens D)
    (f : V → ℂ) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (point : D) (hpoint : point ∈ V) :
    smoothSheafCommRing.eval 𝓘(ℂ) 𝓘(ℂ) D ℂ point
      ((smoothSheafCommRing 𝓘(ℂ) 𝓘(ℂ) D ℂ).presheaf.germ V point hpoint
        (ofHolomorphic D V f hf)) = f ⟨point, hpoint⟩ := by
  exact smoothSheafCommRing.eval_germ V point hpoint (ofHolomorphic D V f hf)

/-- A section of the canonical complex-smooth scalar sheaf is holomorphic. -/
theorem section_holomorphic (D : Opens ℂ) (V : Opens D)
    (representativeSection : (smoothSheafCommRing 𝓘(ℂ) 𝓘(ℂ) D ℂ).presheaf.obj (op V)) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun point : V ↦ representativeSection point) :=
  (smooth_iff_holomorphic D V _).1 representativeSection.2

/-- Smooth scalar sections on an open complex domain are determined pointwise. -/
@[ext] theorem section_ext (D : Opens ℂ) (V : Opens D)
    {first second : (smoothSheafCommRing 𝓘(ℂ) 𝓘(ℂ) D ℂ).presheaf.obj (op V)}
    (h : ∀ point : V, first point = second point) : first = second := by
  apply Subtype.ext
  exact funext h

/-- Holomorphic representatives restrict holomorphically to smaller opens. -/
theorem holomorphic_restrict (D : Opens ℂ) {V W : Opens D} (h : W ≤ V)
    (f : V → ℂ) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun point : W ↦ f ⟨point.1, h point.2⟩) := by
  let representativeSection := ofHolomorphic D V f hf
  let restricted :=
    (smoothSheafCommRing 𝓘(ℂ) 𝓘(ℂ) D ℂ).presheaf.map h.hom.op representativeSection
  have hs := section_holomorphic D W restricted
  exact hs

/-- Bundling a holomorphic representative commutes with canonical restriction. -/
theorem ofHolomorphic_restrict (D : Opens ℂ) {V W : Opens D} (h : W ≤ V)
    (f : V → ℂ) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    (smoothSheafCommRing 𝓘(ℂ) 𝓘(ℂ) D ℂ).presheaf.map h.hom.op
        (ofHolomorphic D V f hf) =
      ofHolomorphic D W (fun point : W ↦ f ⟨point.1, h point.2⟩)
        (holomorphic_restrict D h f hf) := by
  apply section_ext D W
  intro point
  rfl

/-- Holomorphic precomposition between open complex domains is complex-smooth. -/
theorem holomorphic_contMDiff {D E : Opens ℂ} (f : D → E)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ f := by
  have hsubtype : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ (Subtype.val : E → ℂ) :=
    contMDiff_subtype_val
  have hval : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Subtype.val ∘ f) :=
    (hsubtype.mdifferentiable (by norm_num)).comp hf
  have hsmooth := (smooth_iff_holomorphic_open D (Subtype.val ∘ f)).2 hval
  exact (ContMDiff.subtypeVal_comp_iff E f).mp hsmooth

/-- Holomorphic precomposition uses the existing whole sheaf morphism. -/
def holomorphicSheafHom {D E : Opens ℂ} (f : D → E)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    smoothSheafCommRing 𝓘(ℂ) 𝓘(ℂ) E ℂ ⟶
      (TopCat.Sheaf.pushforward _
        (TopCat.ofHom ⟨f, (holomorphic_contMDiff f hf).continuous⟩)).obj
          (smoothSheafCommRing 𝓘(ℂ) 𝓘(ℂ) D ℂ) :=
  (holomorphic_contMDiff f hf).smoothSheafCommRingHom 𝓘(ℂ) E f

/-- The sheaf map induced by a holomorphic map evaluates by precomposition on
the inverse image of an open set. -/
@[simp] theorem holomorphicSheafHom_app_apply {D E : Opens ℂ} (f : D → E)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (V : Opens E)
    (representativeSection : (smoothSheafCommRing 𝓘(ℂ) 𝓘(ℂ) E ℂ).presheaf.obj (op V))
    (point : (Opens.map (TopCat.ofHom ⟨f, (holomorphic_contMDiff f hf).continuous⟩)).obj V) :
    ((holomorphicSheafHom f hf).hom.app (op V) representativeSection :
        (smoothSheafCommRing 𝓘(ℂ) 𝓘(ℂ) D ℂ).presheaf.obj
          (op ((Opens.map (TopCat.ofHom
            ⟨f, (holomorphic_contMDiff f hf).continuous⟩)).obj V))).1 point =
      representativeSection ⟨f point.1, point.2⟩ := rfl

/-- Precomposing a holomorphic representative with a holomorphic map is holomorphic
on the inverse image of its domain. -/
theorem holomorphic_precomp {D E : Opens ℂ} (f : D → E)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (V : Opens E)
    (g : V → ℂ) (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
      (fun point : (Opens.map (TopCat.ofHom
        ⟨f, (holomorphic_contMDiff f hf).continuous⟩)).obj V ↦
        g ⟨f point.1, point.2⟩) := by
  exact section_holomorphic D _
    ((holomorphicSheafHom f hf).hom.app (op V) (ofHolomorphic E V g hg))

/-- The sheaf map takes a holomorphic section to the section represented by
precomposition on the inverse-image open. -/
theorem holomorphicSheafHom_app_ofHolomorphic {D E : Opens ℂ} (f : D → E)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (V : Opens E)
    (g : V → ℂ) (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) :
    (holomorphicSheafHom f hf).hom.app (op V) (ofHolomorphic E V g hg) =
      ofHolomorphic D
        ((Opens.map (TopCat.ofHom ⟨f, (holomorphic_contMDiff f hf).continuous⟩)).obj V)
        (fun point ↦ g ⟨f point.1, point.2⟩)
        (holomorphic_precomp f hf V g hg) := by
  apply section_ext D _
  intro point
  exact holomorphicSheafHom_app_apply f hf V _ point

/-- The existing full locally ringed-space morphism associated to holomorphic
precomposition between open complex domains. -/
def holomorphicLocallyRingedSpaceMap {D E : Opens ℂ} (f : D → E)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    ChartedSpace.locallyRingedSpace 𝓘(ℂ) D ⟶
      ChartedSpace.locallyRingedSpace 𝓘(ℂ) E :=
  ChartedSpace.locallyRingedSpaceMap f (holomorphic_contMDiff f hf)

/-- The full map induced by the holomorphic identity is the identity morphism. -/
@[simp] theorem holomorphicLocallyRingedSpaceMap_id (D : Opens ℂ) :
    holomorphicLocallyRingedSpaceMap (id : D → D) mdifferentiable_id =
      𝟙 (ChartedSpace.locallyRingedSpace 𝓘(ℂ) D) := by
  rfl

/-- The full morphisms, including their sheaf maps, respect composition. -/
theorem holomorphicLocallyRingedSpaceMap_comp {D E F : Opens ℂ}
    (f : D → E) (g : E → F)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) :
    holomorphicLocallyRingedSpaceMap (g ∘ f) (hg.comp hf) =
      holomorphicLocallyRingedSpaceMap f hf ≫
        holomorphicLocallyRingedSpaceMap g hg := by
  rfl

/-- The sheaf component of the full holomorphic-precomposition morphism is
the existing smooth scalar sheaf morphism. -/
theorem holomorphicLocallyRingedSpaceMap_c {D E : Opens ℂ} (f : D → E)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    (holomorphicLocallyRingedSpaceMap f hf).c = (holomorphicSheafHom f hf).hom := rfl

/-- The sheaf component of the full locally ringed-space map precomposes
sections on inverse-image opens. -/
@[simp] theorem holomorphicLocallyRingedSpaceMap_c_app_apply {D E : Opens ℂ} (f : D → E)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (V : Opens E)
    (representativeSection : (smoothSheafCommRing 𝓘(ℂ) 𝓘(ℂ) E ℂ).presheaf.obj (op V))
    (point : (Opens.map (TopCat.ofHom ⟨f, (holomorphic_contMDiff f hf).continuous⟩)).obj V) :
    ((holomorphicLocallyRingedSpaceMap f hf).c.app (op V) representativeSection :
        (smoothSheafCommRing 𝓘(ℂ) 𝓘(ℂ) D ℂ).presheaf.obj
          (op ((Opens.map (TopCat.ofHom
            ⟨f, (holomorphic_contMDiff f hf).continuous⟩)).obj V))).1 point =
      representativeSection ⟨f point.1, point.2⟩ := by
  rw [holomorphicLocallyRingedSpaceMap_c]
  exact holomorphicSheafHom_app_apply f hf V representativeSection point

/-- The full locally ringed-space map takes holomorphic sections to their
precompositions on inverse-image opens. -/
theorem holomorphicLocallyRingedSpaceMap_c_app_ofHolomorphic {D E : Opens ℂ}
    (f : D → E) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (V : Opens E)
    (g : V → ℂ) (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) :
    (holomorphicLocallyRingedSpaceMap f hf).c.app (op V) (ofHolomorphic E V g hg) =
      ofHolomorphic D
        ((Opens.map (TopCat.ofHom ⟨f, (holomorphic_contMDiff f hf).continuous⟩)).obj V)
        (fun point ↦ g ⟨f point.1, point.2⟩)
        (holomorphic_precomp f hf V g hg) := by
  rw [holomorphicLocallyRingedSpaceMap_c]
  exact holomorphicSheafHom_app_ofHolomorphic f hf V g hg

end ComplexLine

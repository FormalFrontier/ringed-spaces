# Finite-regularity scalar function sheaves

The module [`RingedSpaces.FiniteRegularityFunctions`](../RingedSpaces/FiniteRegularityFunctions.lean)
constructs, for each finite `r : ℕ`, a sheaf of scalar-valued `C^r` functions
on a charted space. It also relates its smooth and continuous endpoints to the
existing Mathlib and RingedSpaces sheaves. The companion
[`RingedSpaces.FiniteRegularityFunctions.Maps`](../RingedSpaces/FiniteRegularityFunctions/Maps.lean)
constructs pullback on sections, sheaves, and locally ringed spaces. The companion
[`RingedSpaces.FiniteRegularityFunctions.OpenImmersion`](../RingedSpaces/FiniteRegularityFunctions/OpenImmersion.lean)
compares the locally ringed space of an open subtype with the ambient restriction.

Fix a nontrivially normed field `𝕜 : Type u`, a normed model `EM` over `𝕜`,
a topological model `HM`, and `IM : ModelWithCorners 𝕜 EM HM`. Let
`M : Type u` carry a topology and `[ChartedSpace HM M]`. For an open
`U : Opens M`, the sections of `FiniteRegularityFunctions.sheaf IM M r`
identify with `C^(r : ℕ∞ω)⟮IM, U; 𝓘(𝕜), 𝕜⟯` via
`sectionRingEquiv`. The companion `typeSheaf_obj_eq` and
`typeSheaf_section_contMDiff` characterize the underlying type-sheaf sections.
The functions have the chosen charted-space regularity;
no intrinsic chart-independence assertion is implicit, and there is no
`IsManifold`, `Nonempty M`, or finite-dimensionality hypothesis.

`ofFunction` bundles a function with its `ContMDiff` proof. The equations
`ofFunction_apply` and `sectionRingEquiv_apply`, the predicate
`section_contMDiff`, and `section_ext` give its characteristic section API.
`typeSheaf_forget` identifies the underlying type sheaf with the ring sheaf
after forgetting ring structure. Restriction is `restrict` and satisfies
`restrict_apply`; germs are evaluated by `eval` and `evalHom`, with
`eval_germ` and `evalHom_germ` computing their values at a base point.
The stalk is a local ring: a germ is a unit exactly when it evaluates to a
nonzero scalar. The empty charted carrier is permitted, although no stalk
can be formed at a nonexistent point.
The field and carrier have the same Lean universe, as in the pinned Mathlib
smooth sheaf and the existing continuous-function construction.

## Maps of finite regularity

For charted spaces `M` and `N` over the same field, with respective chosen
models `IM` and `IN`, a map `f : M → N` satisfying
`ContMDiff IM IN (r : ℕ∞ω) f` pulls sections on `U : Opens N` back to
sections on the inverse-image open. The ring homomorphism `precompose`
satisfies `precompose_apply` and `precompose_restrict`; `sheafHom` assembles
these into an arrow from the sheaf on `N` to the pushforward of the sheaf on
`M`. The corresponding `locallyRingedSpaceMap` is local on stalks: it takes
the germ of a section to the germ of its precomposition and preserves
evaluation at the mapped point. `locallyRingedSpaceMap_id` and
`locallyRingedSpaceMap_comp` identify the **entire** arrows, including their
sheaf maps, with identity and composition. These constructions require no
nonempty carrier, manifold-compatibility instance, or finite-dimensional model.

The naturality equations `smoothToFinite_naturality` and
`zeroSheafIso_naturality` compare these pullbacks with Mathlib's smooth
pullback and the existing continuous-function pullback, respectively, as
arrows of sheaves. They do not identify finite-order chosen-chart regularity
with an intrinsic regularity condition or with mere pointwise differentiability.

## Open subtypes and restriction

Let `U : Opens M` carry the charts induced from `M`. For every `r : ℕ`,
`locallyRingedSpaceMap IM IM U M r Subtype.val contMDiff_subtype_val`
is an open immersion of locally ringed spaces. Its section maps are
isomorphisms over the images of opens in `U`: every finite-`C^r` scalar
section on such an inverse image descends to the image open using the
induced charts. The comparison
`restrictLocallyRingedSpaceIso IM M r U` identifies
`(locallyRingedSpace r IM M).restrict U.isOpenEmbedding` with
`locallyRingedSpace r IM U`. The equalities
`restrictLocallyRingedSpaceIso_hom_ofRestrict` and
`restrictLocallyRingedSpaceIso_inv_ofRestrict` express the two factorizations
of the entire inclusion and canonical restriction morphisms, not only their
underlying continuous maps. Empty subtypes and order zero are included.
No manifold, nonempty-carrier, or finite-dimensionality hypothesis is required;
the assertion does not extend to arbitrary open embeddings without
compatibility with the chosen charts.

## Smooth sections and zero order

Mathlib's `smoothSheafCommRing IM 𝓘(𝕜) M 𝕜` has a canonical arrow
`smoothToFinite (IM := IM) (M := M) r` to the finite-order sheaf. On each open, the
`smoothToFiniteSection` ring homomorphism weakens `ContMDiff` order from
`∞` to `r`, preserving values and commuting with restriction. Its stalk
arrow `smoothToFiniteStalk` takes a represented germ to the germ of the
weakened section, commutes with evaluation, and is local: a smooth germ
is invertible exactly when its image is invertible.

At `r = 0`, `contMDiff_zero_iff` identifies zero-order scalar maps with
continuous ones. The two section conversions `zeroToContinuous` and
`continuousToZero` preserve values, commute with open restriction, and
are inverses. They are the components of the natural ring-sheaf
isomorphism `zeroSheafIso (IM := IM) (M := M)` with the **existing**
`ContinuousFunctions.sheaf M 𝕜`, not a second continuous-function sheaf.
`zeroToContinuousStalk` takes germs to their converted germs and commutes
with the two evaluation homomorphisms. It preserves and reflects units
and is a local homomorphism.

The [ordinary-import examples](../RingedSpacesTests/FiniteRegularityFunctions.lean)
include the unit germ of the real `C¹` constant two, the nonunit germ of
the identity at zero, a smooth constant under order weakening, and the
zero-order absolute-value function restricted to `(-∞, 1)` and evaluated
at zero. Here `C¹` means continuously differentiable in the `ContMDiff`
API, rather than merely differentiable at a single point. Only finite
natural orders are considered, not analytic or infinite orders as outputs.
The [map examples](../RingedSpacesTests/FiniteRegularityFunctionsMaps.lean) include a
nonconstant real `C¹` translation on a proper open, its backward germ and
evaluation, whole-arrow identity and composition, a smooth comparison at
order one, an absolute-value comparison at order zero, and a map from the
empty charted carrier.

The finite sheaf and local-ring arguments adapt Heather Macbeth and Adam
Topaz's Mathlib smooth-sheaf work (2023, Apache-2.0), including the
continuous-function sheaf infrastructure credited to Kim Morrison,
Johan Commelin and other Mathlib contributors. The comparisons use
Mathlib's `ContMDiff.of_le` and `contMDiff_zero_iff`, and the continuous
endpoint uses the RingedSpaces [continuous-function construction](continuous-functions.md).

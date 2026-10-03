# Continuous functions as ringed and locally ringed spaces

The modules [`RingedSpaces.ContinuousFunctions`](../RingedSpaces/ContinuousFunctions.lean)
and [`RingedSpaces.ContinuousFunctions.OpenImmersion`](../RingedSpaces/ContinuousFunctions/OpenImmersion.lean)
give a sheaf of continuous ring-valued functions, evaluation of its germs,
continuous-map morphisms and open-immersion comparisons. Import either leaf
directly or import the aggregate `RingedSpaces` for both. All declarations below
live in the existing `ContinuousFunctions` namespace.

## General topological commutative rings

Fix `X R : Type u`, `[TopologicalSpace X]`, `[CommRing R]`,
`[TopologicalSpace R]` and `[IsTopologicalRing R]`. The sheaf
`ContinuousFunctions.sheaf X R` has ring sections consisting of continuous
functions from each open subset of `X` into `R`. Its presheaf stalk at `x : X`
is `stalk X R x`; `evalHom X R x` evaluates germs in `CommRingCat`, and
`eval X R x : stalk X R x →+* R` is the underlying ring homomorphism.
`eval_germ`/`evalHom_germ` evaluate a representative, while `eval_surjective`
exhibits any coefficient as the value of a constant germ. A nontrivial `R`
therefore gives nontrivial stalks, but nontriviality is **not** needed for the
sheaf, evaluation or the ringed-space constructions.

For another topological space `Y : Type u`, a map `f : X → Y` and
`hf : Continuous f`, the open `inverseImage X Y f hf U` is the preimage of
`U : Opens Y`. The ring homomorphism `precompose X R Y f hf U` sends a section
`s` to the section `x ↦ s (f x)`; `precompose_apply` states its pointwise formula.
`sheafHom X R Y f hf` packages those *same* section maps as a morphism into
the pushforward sheaf. They determine the **full** morphism
`ringedSpaceMap X R Y f hf : ringedSpace X R ⟶ ringedSpace Y R`.
Its identities `ringedSpaceMap_id` and `ringedSpaceMap_comp` are equalities of
ringed-space morphisms, including their sheaf components, not merely of bases.
The `ringedSpaceMap_stalkMap_germ` theorem computes the pulled-back germ.

The direction on stalks is contravariant even though the morphism points from
`X` to `Y`: at `x : X`, `(ringedSpaceMap X R Y f hf).hom.stalkMap x`
maps **from** the stalk at `f x` on `Y` **to** the stalk at `x` on `X`.
The exact evaluation triangle is

```lean
(ringedSpaceMap X R Y f hf).hom.stalkMap x ≫ evalHom X R x =
  evalHom Y R (f x)
```

as `ringedSpaceMap_stalkMap_evalHom` states. The empty base, empty opens and
subsingleton (including zero) coefficient rings remain legitimate. Neither
`Nontrivial R`, `Field R`, `T1Space R` nor separation of the bases is imposed.

## Locality over a topological field

Now take a field `K : Type u` with `[TopologicalSpace K]`,
`[IsTopologicalDivisionRing K]` and `[T1Space K]`. For any `x : X`,
`isUnit_stalk_iff X K x s` says that a germ is a unit precisely when its value
is nonzero. A representative nonzero at `x` remains nonzero on a neighborhood:
the nonzero locus is open by `T1Space K`, and its reciprocal is continuous by
the topological division-ring structure. Thus `nonunits_stalk` identifies the
nonunits with `RingHom.ker (eval X K x)`, giving the
`instLocalRingStalk` instance and `locallyRingedSpace X K`.
Evaluation need not be injective: on the real line at zero, the identity
function and zero have distinct germs but equal values.

For any continuous `f : X → Y`, `locallyRingedSpaceMap X K Y f hf` is a **full
locally ringed-space morphism** using the existing precomposition sheaf map.
`stalkMap_evalHom` gives the same backward stalk-evaluation triangle;
`stalkMap_germ` gives the representative formula and `stalkMap_isLocalHom`
the local homomorphism property. Both `locallyRingedSpaceMap_id` and
`locallyRingedSpaceMap_comp` identify full morphisms, not just carrier maps.
The equation `forget_locallyRingedSpaceMap` identifies the image under
`LocallyRingedSpace.forgetToSheafedSpace` with **the same** general-ring
`ringedSpaceMap X K Y f hf` (the forgetful target is the underlying
sheafed/ringed-space morphism); no second section-map construction is used.

The T1 hypothesis matters: over the indiscrete two-point space with values in
an indiscrete nontrivial field, a stalk can be a product of two fields and need
not be local. This is a counterexample to dropping T1, not an additional
formalized theorem. No norm, completeness or base-space separation is required.

## Open embeddings and restriction

For `U X R : Type u` with topologies on both spaces and the *general-ring*
hypotheses above, let `j : U → X` and `hj : IsOpenEmbedding j`. The theorem
`ringedSpaceMap_c_iso U X R j hj V` makes the actual precomposition component
an isomorphism over the image of every `V : Opens U`. The instance
`ringedSpaceMap_isOpenImmersion` applies the open-immersion criterion to the
**actual** `ringedSpaceMap U R X j hj.continuous`. Its inverse on sections is
precomposition with the inverse homeomorphism from `j(V)` to its preimage. The
argument works for empty sources and opens, zero or subsingleton coefficient
rings and non-T1 coefficient topologies; it assumes no separation of `U` or
`X` and does not assert a local-ring structure on stalks.

The existing `locallyRingedSpaceMap_c_iso U X K j hj V` specializes the same
section argument via `forget_locallyRingedSpaceMap`. With the *T1 topological
field* hypotheses, `locallyRingedSpaceMap_isOpenImmersion` applies it to the
actual locally ringed-space morphism, without changing the field-facing API.

For any `A : Opens X` and general-ring coefficients, mathlib directly gives
the comparison (oriented from the intrinsic subtype to the restriction).
The snippets below use `open ContinuousFunctions`. Make the open-immersion
instance local **before elaborating** the generic comparison or a proposition
that contains it, as in the linked root-only client:

```lean
letI := ringedSpaceMap_isOpenImmersion
  A X R Subtype.val A.isOpenEmbedding';
  (SheafedSpace.IsOpenImmersion.isoRestrict
      (ringedSpaceMap A R X Subtype.val A.isOpenEmbedding'.continuous) :
    ringedSpace A R ≅ (ringedSpace X R).restrict A.isOpenEmbedding)
```

The same mathlib API supplies both **full-morphism** equations:

```lean
letI := ringedSpaceMap_isOpenImmersion
  A X R Subtype.val A.isOpenEmbedding';
  (SheafedSpace.IsOpenImmersion.isoRestrict
      (ringedSpaceMap A R X Subtype.val A.isOpenEmbedding'.continuous)).hom ≫
    (ringedSpace X R).ofRestrict A.isOpenEmbedding =
      ringedSpaceMap A R X Subtype.val A.isOpenEmbedding'.continuous

letI := ringedSpaceMap_isOpenImmersion
  A X R Subtype.val A.isOpenEmbedding';
  (SheafedSpace.IsOpenImmersion.isoRestrict
      (ringedSpaceMap A R X Subtype.val A.isOpenEmbedding'.continuous)).inv ≫
    ringedSpaceMap A R X Subtype.val A.isOpenEmbedding'.continuous =
      (ringedSpace X R).ofRestrict A.isOpenEmbedding
```

Here `A.isOpenEmbedding` supplies the `TopCat` restriction arrow, while
`A.isOpenEmbedding'` supplies continuity of the subtype function. The generic
comparison and its triangles require no newly named restriction construction.

With the T1 topological-field hypotheses and `A : Opens X`, the canonical
comparison is oriented **from the restriction
of the ambient space to the intrinsic open subtype**:

```lean
restrictLocallyRingedSpaceIso X K A :
  (locallyRingedSpace X K).restrict A.isOpenEmbedding ≅ locallyRingedSpace A K
```

The two full-morphism equalities, in their respective domains, are

```lean
(restrictLocallyRingedSpaceIso X K A).hom ≫
    locallyRingedSpaceMap A K X Subtype.val A.isOpenEmbedding'.continuous =
  (locallyRingedSpace X K).ofRestrict A.isOpenEmbedding

(restrictLocallyRingedSpaceIso X K A).inv ≫
    (locallyRingedSpace X K).ofRestrict A.isOpenEmbedding =
  locallyRingedSpaceMap A K X Subtype.val A.isOpenEmbedding'.continuous
```

These are `restrictLocallyRingedSpaceIso_hom_ofRestrict` and
`restrictLocallyRingedSpaceIso_inv_ofRestrict`. The unprimed embedding is the
`TopCat` restriction input; the primed embedding supplies the continuity of
the subtype function. They compare the canonical restriction arrow with the
actual precomposition inclusion, including sheaf maps; there is no new
restriction construction.

## Import and build

The [ring-valued root-only examples](../RingedSpacesTests/ContinuousFunctions.lean) exercise
general-ring precomposition, stalk evaluation, identity/composition, the empty
base and subsingleton rings, alongside field locality and forgetting. The
[open-immersion root-only examples](../RingedSpacesTests/ContinuousFunctionsOpenImmersion.lean)
exercise general-ring open embeddings, mathlib's full restriction comparison
and triangles, plus the existing field-specific inclusion factorizations. A consumer
may start either of two separate files with one of these imports:

```lean
module
public import RingedSpaces
```

```lean
module
public import RingedSpaces.ContinuousFunctions.OpenImmersion
```

For example, after either import (and `open CategoryTheory TopologicalSpace
AlgebraicGeometry`), the test files demonstrate statements such as
`ContinuousFunctions.ringedSpaceMap_id X R` and
`ContinuousFunctions.restrictLocallyRingedSpaceIso X K A`; for the general-ring
sheaf alone, use `public import RingedSpaces.ContinuousFunctions`, and for
general-ring open immersions use the open-immersion leaf or root.
The repository pins Lean `v4.34.0-rc2` and mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`. In an authorized pinned
build environment, retrieve the matching precompiled cache **first**:

```sh
lake exe cache get
lake build +RingedSpacesTests.ContinuousFunctions +RingedSpacesTests.ContinuousFunctionsOpenImmersion
lake build
```

For a stricter warning check after fetching the cache, run
`lake --wfail build +RingedSpacesTests.ContinuousFunctions +RingedSpacesTests.ContinuousFunctionsOpenImmersion`.
This treats warnings as failures; the ordinary build above neither suppresses
warnings nor asserts that this library is warning-free.

Do not fall back to a cold mathlib build if cache retrieval fails. These
declarations use one universe for spaces and coefficients; there is no general
mixed-universe theorem, manifold/chart equivalence or smooth, holomorphic or
differentiable analogue in this API.

The sheaf and precomposition follow mathlib's continuous-function constructions
by Kim Morrison, Andrew Yang, Johan Commelin and other contributors. The stalk
locality and restriction comparison adapt Heather Macbeth's sheaf and
open-subtype methods; the generic sheaf-of-functions infrastructure includes
work by Adam Topaz and other mathlib contributors. See the retained notices in
the Lean modules and [`NOTICE.md`](../NOTICE.md) for roles and license details.

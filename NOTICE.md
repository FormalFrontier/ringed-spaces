# Attribution and redistribution

Formal Frontier contributors prepared this library's original Lean development,
examples, mathematical expositions, README, metadata and this notice for
distribution under the unmodified root Apache-2.0 `LICENSE`. Authorship and an
Apache license do not assert or identify a copyright owner. Atlas maintains the
ringed-space library; mathematical proofs, examples and documentation have
distinct contributors. Source-specific correspondence and research records are
not part of this library.

`RingedSpaces/OpenCover.lean` retains the authentic 2022 Andrew Yang copyright,
license and author notice from mathlib's
`Mathlib/AlgebraicGeometry/Gluing.lean`: its generic categorical transition-map
construction was adapted, not merely cited. The upstream file is distributed
under Apache-2.0 at mathlib commit
`83abb3e776bdefcbc447a1e44d0debe4010039e5` (see its retained header and
mathlib's license). The surrounding open-cover comparison and full-morphism
proofs are separate project developments. Other mathlib categories, sheaves,
Kan extensions, module colimits and tensor products are imported as the pinned
external dependency, not copied into this repository; their original mathlib
authorship remains with the upstream project. In particular, the native
varying-ring module-colimit API used here credits Joël Riou in mathlib.

`RingedSpaces/ContinuousFunctions.lean` and
`RingedSpaces/ContinuousFunctions/OpenImmersion.lean` retain the upstream
copyright notices for Kim Morrison (2020) and Heather Macbeth (2023),
their Apache-2.0 notice and adaptation credit. The sheaf and continuous-function
methods build on work by Kim Morrison, Andrew Yang, Johan Commelin, Adam Topaz
and other mathlib contributors; the stalk and open-subtype approaches adapt
Heather Macbeth's methods. Formal Frontier contributors developed and extended
the reusable mathematical proofs, concrete examples and unified guide. These
contributions do not claim to originate the upstream mathematics or own its
copyright.

`RingedSpaces/FiniteRegularityFunctions.lean` retains Heather Macbeth's
authentic 2023 copyright notice and credits Adam Topaz alongside Formal
Frontier contributors. Its finite-order sheaf and local-stalk arguments adapt
the Apache-2.0 mathlib smooth-sheaf work of Macbeth and Topaz, while its
endpoint comparisons reuse mathlib's smooth scalar sheaf and this library's
continuous-function sheaf. The chosen-chart finite-order results and their
concrete examples are separate library developments; this attribution does not
assert copyright ownership.

The repository's root `LICENSE` is the complete Apache-2.0 license text.
`formalization.yaml` uses the publicly distributed Apache-2.0 v0.4
formalization.yaml schema and template as a metadata format, not as copied
mathematical text. The mathematical prose, tests and examples in this tree are
project contributions. `docs/API.md` is a
navigation- and prose-adjusted historical Markdown adaptation of native
declaration signatures and project docstrings, using separately built
`leanprover/doc-gen4` at
`97d4ecdfc8e09e7f511724c25e303d448de6a3db`. The shipped adapter in
`scripts/generate_api.py` credits Atlas's multivariate-polynomials and
quadratic-algebras recipes and Anchor's original ideal-completion recipe, all
project contributions under Apache-2.0. Native HTML, Lean `Init` output,
scripts/styles/fonts and the upstream debounce snippet are **not** shipped.
The doc-gen4 tool remains separately credited under its Apache-2.0 license;
no rights claim about its excluded generated-site assets is inferred.

## Mathematical and software attribution

Formal Frontier contributors used agent-assisted Lean development and kernel
checking. Pooled Git author names do not establish sole mathematical authorship
or copyright ownership. The contributions below distinguish original work from
adaptations and imported dependencies.

| Mathematics or artifact | Original and adapted contributions |
| --- | --- |
| Open restrictions, indexed gluing, literal intersections and full inverse-image factorization | Formal Frontier contributors developed the ringed-space proofs, intersection bridge and inverse-image construction; the generic gluing transition construction is an adaptation of Andrew Yang's credited mathlib work, not an original project invention. |
| Module presheaf/sheaf scalar extension, right-factor tensor symmetry and continuous presheaf inverse image | Formal Frontier contributors proved the scalar-extension and inverse-image results and supplied examples, native modules and public-root exports. The underlying mathlib categories, sheaves and tensor products are imported dependencies, not project-authored copies. |
| Continuous module-sheaf inverse image and bundled Hom adjunction | Formal Frontier contributors developed library proofs, direct-import examples and reader guides informed by earlier research on module actions and Hom/coherence. |
| Full ringed-space module pushforward and explicit right-tensor pullback | Formal Frontier contributors proved the comparisons and adjunction and prepared examples, public exports and documentation. Joël Riou's varying-ring module-colimit and module-sheaf work remains credited to mathlib. |
| Pullback coherence and arbitrary-square mates | Formal Frontier contributors proved the reusable coherence results, adapted earlier mathematical prototypes and prepared public-root examples and documentation. |
| Square-mate horizontal and vertical pasting | Formal Frontier contributors proved the pasting laws and supplied the library module, fixture, public-root examples and guide; earlier proof prototypes are distinct contributions. |
| Constant-closed full morphisms and all-affine-map non-affineness | Formal Frontier contributors supplied the constructor, extension proofs, examples and guide. |
| Continuous-function sheaves, evaluation, ringed and locally ringed-space maps, and open immersions | Mathlib contributors' sheaf and open-subtype methods are retained and credited in both Lean modules. Formal Frontier contributors proved the extensions and supplied concrete examples and a standalone guide. |
| Finite-order scalar-function sheaves and endpoint comparisons | Heather Macbeth and Adam Topaz's smooth-sheaf methods inform the chosen-chart construction; Formal Frontier contributors developed the finite-order section, stalk and comparison proofs and concrete clients while reusing the existing smooth and continuous sheaves. |
| Documentation, license and native API adaptation | Documentation and native-module work include contributions distinct from the mathematical originals. Anchor originated the ideal-completion doc-generation recipe; Atlas adapted it for multivariate polynomials and quadratic algebras and maintains the project adapter. |

The historical [`docs/API.md`](docs/API.md) reflects its original source
snapshot rather than the complete current API. Its adapted Markdown prose is
not new generation or a claim of source coverage.

## Mathematical sources

Ravi Vakil's *The Rising Sea: Foundations of Algebraic Geometry*, October 21,
2025 draft, Definition 4.3.9 (p. 142) motivates the scalar-preserving
reconstruction results; §§2.2.13, 4.3.1 and 4.3.7 supply the ringed-space and residue
conventions. This library develops a scalar-preserving strengthening, not a
transcription of a generalized theorem or proof stated there. Its evaluation
argument uses a unit contradiction, and recovery of smoothness uses finite
continuous-linear coordinates and smooth scalar sections. Those project proofs
are distinct from the motivating discussion and from the Mathlib formalization
methods below.

The same definition also motivates the boundaryless local-ball and
holomorphic-function models, fixed-atlas regularity and comparisons of specified
compatible atlases. The chart and canonical scalar-sheaf constructions and their
proofs are project developments using the Mathlib and Complex Analysis APIs
credited below, not generalized theorems or proofs attributed to Vakil. The
complex-regularity bridge concerns a given boundaryless finite-dimensional
complex atlas; the sheaf comparisons concern canonical scalar sheaves, not
recovery of an arbitrary supplied sheaf.

Definition 4.3.9 also motivates the real-function local models and the
finite-regularity scalar-function constructions; it is not a printed general
finite-`C^r` theorem. The project developments distinguish continuous functions
over topological commutative rings from the T1 topological-field hypotheses for
local stalks and locally ringed-space maps. Finite regularity uses a chosen
atlas and a finite natural order, induced charts on open subtypes, and entire
boundaryless chart balls. These constructions and proofs use the separately
credited smooth-sheaf, stalk and chart methods of Mathlib; they do not identify
an arbitrary structure sheaf with a canonical scalar sheaf.

Exercise 7.2.G (p. 206), with conventions 7.2.1 and the affine-induced contrast
in Exercise 7.2.F, motivates full nonlocal ringed-space morphisms. The
generalized constant-closed-point constructors, fixed-base classification and
non-affineness against every affine-induced full morphism are project
developments, not generalized theorems or proofs attributed to Vakil. Their
full sheaf maps are essential, and no locally ringed-space or scheme-morphism
assertion follows.

Exercise 7.2.D(a)–(f) supplies mathematical motivation for the inverse-image
factorization and ringed-module functors. The factorization in part (a) uses
Mathlib's inverse-image sheaf adjunction and is not a categorical fiber product.
For parts (b), (c) and (e), §2.6.4 / Exercise 2.6.K(a) (p. 92) describes tensor
presheaves followed by sheafification; §2.7.2 (p. 93) gives the temporary
inverse-image presheaf. The project's presheaf inverse image and linear Hom
adjunction generalize the coefficient setting to `RingCat`; actual
sheafification and coefficient-unit coherence are distinct further constructions.
Fixed-space right-factor tensors and their symmetry enable these functors;
they are not raw tensors on arbitrary sheaf sections or a separately numbered
fixed-space theorem in Vakil. The full ringed-space pullback uses the whole
structure map, sheafified inverse image and right tensor, with an adjunction
and an isomorphism to Mathlib's chosen pullback. Project constructions and
proofs remain distinct from Joël Riou's imported module and sheaf methods.

Part (d) concerns a natural isomorphism, not equality of pullback functors;
canonical unit and associativity coherence use further project and Mathlib
theory. Part (f) and §2.7.4 (p. 94) motivate the push–pull mate of an arbitrary
full commutative square, without a Cartesian or invertibility assertion.
Horizontal and vertical pasting extend this project API. These citations do
not attribute the generalized constructions or their proofs to Vakil.

## Prior formalizations

The Mathlib references below are at version
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, under Apache-2.0. Adaptations of
upstream methods are distinguished from direct use of imported constructions;
all retained notices and contributor credits above continue to apply.

| Methods used in this library | Mathlib formalization and contributors |
| --- | --- |
| Adapted generic gluing transitions; reused open-immersion API | Andrew Yang: [gluing](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/AlgebraicGeometry/Gluing.lean) and [open immersions](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Geometry/RingedSpace/OpenImmersion.lean). |
| Adapted continuous-function presheaves and separate local-predicate machinery; the sheaf proof is supplied here | Kim Morrison and Andrew Yang: [continuous-function presheaves](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Topology/Sheaves/CommRingCat.lean); Johan Commelin, Kim Morrison and Adam Topaz: [local predicates](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Topology/Sheaves/LocalPredicate.lean). |
| Reused smooth scalar sheaf and evaluation; adapted finite-order scalar-sheaf methods | Heather Macbeth and Adam Topaz: [smooth scalar sheaves and evaluation](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Geometry/Manifold/Sheaf/Smooth.lean). |
| Reused local-ring and full-morphism constructions; adapted stalk and open-subtype arguments | Heather Macbeth: [locally ringed spaces](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Geometry/Manifold/Sheaf/LocallyRingedSpace.lean). |
| Reused varying-ring module colimits, sheafification and change of rings | Joël Riou: [module colimits](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Algebra/Category/ModuleCat/Presheaf/ColimitFunctor.lean), [sheafification](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Algebra/Category/ModuleCat/Presheaf/Sheafification.lean) and [change of rings](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Algebra/Category/ModuleCat/Sheaf/ChangeOfRings.lean). |
| Reused structure-groupoid, maximal-atlas and chart constructions | Sébastien Gouëzel: [structure groupoids](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Geometry/Manifold/StructureGroupoid.lean) and [charted spaces](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Geometry/Manifold/ChartedSpace.lean). |
| Reused manifold-smoothness and atlas APIs | Sébastien Gouëzel and Floris van Doorn: [smoothness in normed spaces](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Geometry/Manifold/ContMDiff/NormedSpace.lean) and [smooth atlases](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Geometry/Manifold/ContMDiff/Atlas.lean). |
| Reused bundled diffeomorphism structure, differentiability and inverse (`symm`) APIs | Nicolò Cavalleri and Yury Kudryashov: [diffeomorphisms](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Geometry/Manifold/Diffeomorph.lean). |

`RingedSpaces/ChartedSpace/LocalBall.lean`,
`RingedSpaces/ChartedSpace/CompatibleAtlases.lean` and
`RingedSpaces/FiniteRegularityFunctions/LocalBall.lean` reuse this `Diffeomorph`
structure and its differentiability and `symm` APIs. This contribution is
distinct from the chart/atlas interfaces credited above; the local-ball,
mixed-atlas and finite-order proofs are project developments.

The complex regularity modules directly use Formal Frontier's
[Complex Analysis finite-dimensional analyticity formalization](https://github.com/FormalFrontier/complex-analysis/blob/2c0ad1d2ce6d2f815930d64428d66618cb9f122d/ComplexAnalysis/Analysis/Complex/FiniteDimensional.lean)
at version `2c0ad1d2ce6d2f815930d64428d66618cb9f122d`. This credits the
prior Lean result used here; the atlas comparisons and scalar-sheaf applications
are separate developments in this library.

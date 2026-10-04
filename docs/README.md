# API documentation and historical binding

[`API.md`](API.md) is a **navigation- and prose-adjusted historical reference**
retaining native displayed signatures and original nonempty declaration
docstrings from a 33-module snapshot. Its 33 module and 281 declaration links
point to identical old sources at official published commit
`958b340be6cf1a0bc86c2c378352664c9f7cca62`. The absolute GitHub URLs to
the old `Test/` sources remain pinned to that commit; those local paths are
absent from this tree.
This is not a newly generated or complete current API page. The original
generated Markdown SHA256
`31abe5d797e950a0d6df5bc08167634abf872964723c03c85616f417972d0ade`
and the manifest digest apply to the **unmodified** page at that published
snapshot, not to the hand-adjusted page or the current library.
That source carries 282 public source-range names; native doc-gen4 emits 281
records. `AlgebraicGeometry.RingedSpace.OpenCover.rec` is an automatically
generated recursor with no native record and is called out, not invented.
The 122 declarations without native docstrings are labeled explicitly. Every
module in that snapshot has a top-level source docstring. This tree has 82 Lean
files, including 52 tests under `RingedSpacesTests/`, and 14 mathematical guides.
The unchanged historical records remain useful for their original sources;
the current additions are mapped below and in the guides.

## Current API map beyond the historical snapshot

The newer library leaves are exported by the public `RingedSpaces` root.
Direct imports and their guides give narrower dependencies:

| Direct module | Representative API | Mathematical guide |
| --- | --- | --- |
| [`RingedSpaces.Modules.SheafInverseImage`](../RingedSpaces/Modules/SheafInverseImage.lean) | `moduleFunctor`, `comparisonNatIso`, `moduleUnderlyingNatIso`, `actualUnit` | [`sheaf-inverse-image.md`](sheaf-inverse-image.md) |
| [`RingedSpaces.Modules.SheafInverseImageHom`](../RingedSpaces/Modules/SheafInverseImageHom.lean) | `homEquiv`, `adjunction`, `unit_underlying`, `left_triangle`, `right_triangle` | [`sheaf-inverse-image.md`](sheaf-inverse-image.md) |
| [`RingedSpaces.Modules.RingedSpacePushforward`](../RingedSpaces/Modules/RingedSpacePushforward.lean) | `structureMap_original`, `actualUnit_comp_ringSheafMap`, `pushforwardFunctor`, `restrictPushforwardIso` | [`ringed-space-pushforward.md`](ringed-space-pushforward.md) |
| [`RingedSpaces.Modules.RingedSpacePullback`](../RingedSpaces/Modules/RingedSpacePullback.lean) | `pullbackFunctor`, `homEquiv`, `adjunction`, `unit_formula`, `nativeComparison`, `nativeComparison_homEquiv` | [`ringed-space-pullback.md`](ringed-space-pullback.md) |
| [`RingedSpaces.Modules.PullbackCoherence`](../RingedSpaces/Modules/PullbackCoherence.lean) | `pushforwardComp`, `pullbackComp`, `pullbackComp_assoc` | [`ringed-module-coherence-base-change.md`](ringed-module-coherence-base-change.md) |
| [`RingedSpaces.Modules.BaseChange`](../RingedSpaces/Modules/BaseChange.lean) | `pushPull`, `pushPull_identity_normalized` | [`ringed-module-coherence-base-change.md`](ringed-module-coherence-base-change.md) |
| [`RingedSpaces.Modules.BaseChangePasting`](../RingedSpaces/Modules/BaseChangePasting.lean) | `pushPull_pastePullback`, `pushPull_pastePushforward` | [`ringed-module-base-change-pasting.md`](ringed-module-base-change-pasting.md) |
| [`RingedSpaces.ClosedPointHom`](../RingedSpaces/ClosedPointHom.lean) | `hom`, `hom_top_transport`, `ext`, `equiv`, `comp_hom` in `AlgebraicGeometry.RingedSpace.ClosedPointHom` | [`closed-point-hom.md`](closed-point-hom.md) |
| [`RingedSpaces.ClosedPointNonAffine`](../RingedSpaces/ClosedPointNonAffine.lean) | `hom_ne_sheafedSpaceMap_of_isUnit`, `not_exists_sheafedSpaceMap_of_isUnit` in `AlgebraicGeometry.RingedSpace.ClosedPointHom` | [`closed-point-nonaffine.md`](closed-point-nonaffine.md) |
| [`RingedSpaces.ContinuousFunctions`](../RingedSpaces/ContinuousFunctions.lean) | `ContinuousFunctions.sheaf`, `evalHom`, `ringedSpaceMap`, `locallyRingedSpaceMap`, `forget_locallyRingedSpaceMap` | [`continuous-functions.md`](continuous-functions.md) |
| [`RingedSpaces.ContinuousFunctions.OpenImmersion`](../RingedSpaces/ContinuousFunctions/OpenImmersion.lean) | `ContinuousFunctions.locallyRingedSpaceMap_isOpenImmersion`, `restrictLocallyRingedSpaceIso` and both `*_ofRestrict` equalities | [`continuous-functions.md`](continuous-functions.md) |
| [`RingedSpaces.FiniteRegularityFunctions`](../RingedSpaces/FiniteRegularityFunctions.lean) | `FiniteRegularityFunctions.sheaf`, `sectionRingEquiv`, `evalHom`, `zeroSheafIso` | [`finite-regularity-functions.md`](finite-regularity-functions.md) |
| [`RingedSpaces.FiniteRegularityFunctions.Maps`](../RingedSpaces/FiniteRegularityFunctions/Maps.lean) | `FiniteRegularityFunctions.precompose`, `sheafHom`, `locallyRingedSpaceMap`, `smoothToFinite_naturality`, `zeroSheafIso_naturality` | [`finite-regularity-functions.md`](finite-regularity-functions.md) |
| [`RingedSpaces.FiniteRegularityFunctions.OpenImmersion`](../RingedSpaces/FiniteRegularityFunctions/OpenImmersion.lean) | `FiniteRegularityFunctions.restrictLocallyRingedSpaceIso` and both whole-arrow `*_ofRestrict` equalities | [`finite-regularity-functions.md`](finite-regularity-functions.md#open-subtypes-and-restriction) |
| [`RingedSpaces.FiniteRegularityFunctions.LocalBall`](../RingedSpaces/FiniteRegularityFunctions/LocalBall.lean) | `FiniteRegularityFunctions.localBall`, `LocalBall.iso`, and coordinate germ/section evaluation | [`finite-regularity-functions.md`](finite-regularity-functions.md#finite-order-local-balls) |
| [`RingedSpaces.ChartedSpace.LocalBall`](../RingedSpaces/ChartedSpace/LocalBall.lean) | `ChartedSpace.chartLocalBall`, `ChartLocalBall.coord`, `center`, `coord_at_center` | [`chart-local-ball.md`](chart-local-ball.md) |
| [`RingedSpaces.ChartedSpace.SmoothLocalBall`](../RingedSpaces/ChartedSpace/SmoothLocalBall.lean) | `ChartLocalBall.smoothIso`, whole-arrow and full-composite evaluation laws | [`chart-local-ball.md`](chart-local-ball.md) |
| [`RingedSpaces.Complex.Holomorphic`](../RingedSpaces/Complex/Holomorphic.lean) | Complex smoothness and differentiability on finite-dimensional complex open subsets with complete targets | [`README.md`](../README.md) |
| [`RingedSpaces.ChartedSpace.HolomorphicSections`](../RingedSpaces/ChartedSpace/HolomorphicSections.lean) | `ComplexManifold.ofHolomorphic`, restriction, germ evaluation and precomposition on inverse-image opens through full maps; `ComplexLine` specializations | [`README.md`](../README.md) |

The [root-only sheaf client](../RingedSpacesTests/SheafInverseImageRoot.lean) and
[root-only full-morphism client](../RingedSpacesTests/RingedSpaceFullMorphismRoot.lean)
exercise these public exports. The two full-morphism `RootCoexist` tests
retain explicit leaf imports for compatibility, not root-only evidence.
The [root-only constant-closed client](../RingedSpacesTests/ClosedPointHom.lean) exercises
its export without a leaf import.
The [root-only non-affineness client](../RingedSpacesTests/ClosedPointNonAffine.lean) tests
arbitrary field and non-field inducing maps. The
[general-ring](../RingedSpacesTests/ContinuousFunctions.lean) and
[open-immersion](../RingedSpacesTests/ContinuousFunctionsOpenImmersion.lean) clients also
import only `RingedSpaces`. The [finite-regularity](../RingedSpacesTests/FiniteRegularityFunctions.lean)
and [map](../RingedSpacesTests/FiniteRegularityFunctionsMaps.lean) clients, as well as the
[open-subtype](../RingedSpacesTests/FiniteRegularityFunctionsOpenImmersion.lean) and
[local-ball](../RingedSpacesTests/FiniteRegularityFunctionsLocalBall.lean) clients,
the [smooth chart-ball](../RingedSpacesTests/ChartedSpaceSmoothLocalBall.lean),
and [holomorphic section](../RingedSpacesTests/HolomorphicSections.lean)
clients likewise exercise the public root. All 52 tests are among the 54 literal default
targets, alongside the library aggregate and examples. The historical
generated API snapshot and manifest remain unchanged and cover none of the
new leaves.

## Reproduction and binding

[`api-manifest.json`](api-manifest.json) binds its 33 historical module source files,
`lean-toolchain`, the **historical** `lakefile.toml` and the nine-dependency
`lake-manifest.json` by exact hash; it also binds every native module record,
the 282-name loaded inventory, generator revision and generated Markdown bytes. The analyzed
source snapshot is `fc4581c6b42eb3b2c3dbeb714a8c76c51934d4fb`, tree
`c330aa042beae57328c5428193f2bfa5c4ff336d`. The earlier source-only
generation against `53ab3568ea99f564db64c551b5c38d897caca78b` remains
preserved in the previous author's evidence, not attributed to this input. The pinned
tool is `leanprover/doc-gen4` at
`97d4ecdfc8e09e7f511724c25e303d448de6a3db`, built using the project's
Lean `v4.34.0-rc2`. The native source identifier is
`git-source:<analyzed-source-revision>/<relative-Lean-path>`. This is a
content-addressed **identifier**, not a network retrieval URL or a claim
that the analyzed development commit is a published release commit. The
adapter checks the exact native module, name, kind, complete displayed header,
source path, revision and loaded source line, then checks every real source
and configuration byte against the Git object. For a standalone parentless
checkout without that object it instead checks the exact committed manifest
and all current committed inputs; a present but wrong object is never treated
as absent. All 36 input hashes match at the official historical snapshot. In
this tree, only 11 historical inputs still match; `RingedSpaces.lean`,
`RingedSpaces/InverseImage.lean`, and `lakefile.toml` differ, while the 22 old
`Test/*.lean` input paths are absent after the move to `RingedSpacesTests/`.
The old manifest cannot authenticate this tree, its added modules or the
hand-adjusted API page. Provider-neutral generation records and earlier
provider checks are separate historical evidence, not a current-tree check.

To reproduce the **unmodified original** historical output, use a separate
checkout of official published commit
`958b340be6cf1a0bc86c2c378352664c9f7cca62`, which contains the matching
original inputs, manifest, adapter and generated Markdown. That official
snapshot is parentless: analyzed development revision
`fc4581c6b42eb3b2c3dbeb714a8c76c51934d4fb` is not in its Git history.
A clean official checkout therefore uses the adapter's committed-manifest
binding for the missing analyzed object, as described above. The identifier
still binds the historical source bytes; it is not a fetchable ancestor.
The unchanged adapter first compares the current complete Lean module-path set
with its fixed 33-module historical inventory, before reading source inputs or
native records. This tree has Lean paths outside that old set and lacks the 22
old `Test/*.lean` paths, so it fails that inventory check; the changed and missing
input paths also prevent a historical source binding. Do **not** run the following
historical recipe against this tree. It is optional for reproducing **only**
the frozen historical original output, not this hand-adjusted page and not a
prerequisite for building or reviewing this tree.
If reproducing the snapshot separately, first run `lake exe cache get` with
the pinned toolchain and mathlib revision.
Build the pinned `leanprover/doc-gen4` Git revision above with the same Lean
toolchain, and set `DOCGEN` to its executable and `NATIVE_OUTPUT` to a fresh
temporary output directory. The following complete native command recipe
uses only the committed manifest and these two local paths:

```sh
export DOCGEN=/path/to/pinned/doc-gen4/.lake/build/bin/doc-gen4
export NATIVE_OUTPUT=/path/to/fresh/native-output
python3 -B - <<'PY'
import json
import os
from pathlib import Path
import subprocess

manifest = json.loads(Path('docs/api-manifest.json').read_text())
modules = manifest['modules']
revision = manifest['analyzed_source_revision']
root = Path(os.environ['NATIVE_OUTPUT'])
analysis = root / 'analysis'
rendered = root / 'rendered'
analysis.mkdir(parents=True)
rendered.mkdir(parents=True)

subprocess.run(['lake', 'build', *modules], check=True)
def native(*command):
    subprocess.run(['lake', 'env', os.environ['DOCGEN'], *map(str, command)], check=True)

native('genCore', '--build', analysis, 'Init', 'api-docs.db')
for module in modules:
    path = module.replace('.', '/') + '.lean'
    native('single', '--build', analysis, module, 'api-docs.db', f'git-source:{revision}/{path}')
native('bibPrepass', '--build', rendered, '--none')
native('fromDb', '--build', rendered, '--manifest', rendered / 'manifest.json',
       analysis / 'api-docs.db', *modules)
PY
python3 -B scripts/generate_api.py --native-data "$NATIVE_OUTPUT/rendered/doc-data" \
  --source-revision fc4581c6b42eb3b2c3dbeb714a8c76c51934d4fb --check
python3 -B scripts/test_generate_api.py --native-data "$NATIVE_OUTPUT/rendered/doc-data"
```

No private provider or native HTML site is needed to run this source-only
recipe in the published checkout. Do not substitute a different origin
scheme, revision, source path or source line: the adapter rejects them.
The source revision must identify the exact analyzed `.lean`/config bytes for
that historical checkout, even if a later commit only edits documentation.
In that separate checkout, if the analyzed revision exists in Git, its
committed bytes are compared to every present input. A historical checkout
without that object, including a clean checkout of the official parentless
snapshot, instead checks the regenerated manifest
against its own committed manifest and every current committed input and generator;
present-but-wrong history never triggers this fallback. The published
evidence records the native inputs, bytes, tool and checks. Source changes
require a fresh generation, not a stale manifest or parent assumption.

No HTML site, mathlib dependency pages, Lean `Init` pages, CDNs, JavaScript,
fonts or source scans ship in the Markdown release artifact. Their earlier
native diagnostic output and explicit dependency-link limitations remain
development evidence rather than a claim about this source-only package.
The adapted generator credits Atlas's multivariate-polynomials and
quadratic-algebras adapters and Anchor's original ideal-completion recipe;
the historical output is not a certification of current library content.

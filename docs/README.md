# Source-only API documentation

[`API.md`](API.md) retains native displayed signatures and original nonempty
docstrings for every generated public declaration in the historical 33-module
snapshot. It links to the **relative** source path for each recorded declaration
and module, so it works without a development-history parent or Forgejo session.
That source carries 282 public source-range names; native doc-gen4 emits 281
records. `AlgebraicGeometry.RingedSpace.OpenCover.rec` is an automatically
generated recursor with no native record and is called out, not invented.
The 122 declarations without native docstrings are labeled explicitly. Every
module in that snapshot has a top-level source docstring. The September 26,
2026 combined candidate had 55 Lean files (33 historical files, eight from
sheaf preparation, 13 from full-morphism preparation, and one new root-only
client), 40 `Test` modules and seven mathematical guides. The pasting addition
brings this tree to 60 Lean files, 42 `Test` modules and nine mathematical guides.
The historical
`RingedSpaces` root and `lakefile.toml` have since changed: the old root's
record and input hashes do **not** describe or certify this whole tree.
The other unchanged historical module records remain useful within their
recorded scope; added APIs are mapped below and in the guides.

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

The [root-only sheaf client](../Test/SheafInverseImageRoot.lean) and
[root-only full-morphism client](../Test/RingedSpaceFullMorphismRoot.lean)
exercise these public exports. The two full-morphism `RootCoexist` tests
retain explicit leaf imports for compatibility, not root-only evidence.
`lakefile.toml` lists all 42 shipped tests among its 44 literal defaults,
including intentional legacy and diagnostic audit clients.

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
as absent. This 60-file tree changes `RingedSpaces.lean` and
`lakefile.toml`: their two historical input hashes **do not match** the current
files. The old manifest does not authenticate this tree; its other 34
historical inputs remain unchanged. The earlier private-provider native
generation and 33 actual Git GET comparisons remain **separate historical evidence**, not the source of
the provider-neutral records used for this Markdown. The renewed historical
records, commands and compiled-part receipts are separate evidence, not a
check of the present 60-file tree.

To reproduce this scoped historical snapshot, use a separate checkout of accepted
revision `5795205b8da2982b6cd70ea17d2f5ec721ac3819`, which contains the
matching committed manifest, adapter and generated Markdown, with analyzed
source revision `fc4581c6b42eb3b2c3dbeb714a8c76c51934d4fb` in its Git
history. The unchanged adapter explicitly rejects this
60-file tree's 27 additional Lean files at its complete-inventory
guard; do **not** run the following historical 33-module recipe against this
tree. It is optional for reproducing **only** the frozen historical
snapshot, not a prerequisite for building or reviewing this tree.
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

No private provider, native HTML site or hypothetical public GitHub commit
is needed to run this source-only recipe. Do not substitute a different origin
scheme, revision, source path or source line: the adapter rejects them.
The source revision must identify the exact analyzed `.lean`/config bytes for
that historical checkout, even if a later commit only edits documentation.
In that separate checkout, if the analyzed revision exists in Git, its
committed bytes are compared to every present input. A synthetic parentless
historical checkout without that object instead checks the regenerated manifest
against its own committed manifest and every current committed input and generator;
present-but-wrong history never triggers this fallback. The published
evidence records the native inputs, bytes, tool and checks. Source changes
require a fresh generation, not a stale manifest or parent assumption.

No HTML site, mathlib dependency pages, Lean `Init` pages, CDNs, JavaScript,
fonts or source scans ship in the Markdown release artifact. Their earlier
native diagnostic output and explicit dependency-link limitations remain
development evidence rather than a claim about this source-only package.
The adapted generator acknowledges Atlas's accepted multivariate-polynomials
and quadratic-algebras recipes and Anchor's original ideal-completion recipe;
earlier code acceptances alone do not certify this historical generated snapshot.

# Source-only API documentation

[`API.md`](API.md) retains native displayed signatures and original nonempty
docstrings for every generated public declaration in all 33 shipped Lean
modules. It links to the **relative** source path for each declaration and
module, so it works without a development-history parent or Forgejo session.
The source carries 282 public source-range names; native doc-gen4 emits 281
records. `AlgebraicGeometry.RingedSpace.OpenCover.rec` is an automatically
generated recursor with no native record and is called out, not invented.
The 122 declarations without native docstrings are labeled explicitly. Every
module now has a top-level source docstring. The mathematical guides
in this directory and the root README remain the primary explanations.

## Reproduction and binding

[`api-manifest.json`](api-manifest.json) binds all 33 module source files,
`lean-toolchain`, `lakefile.toml` and the nine-dependency `lake-manifest.json`
by exact hash; it also binds every native module record, the 282-name loaded
inventory, generator revision and generated Markdown bytes. The analyzed
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
as absent. The earlier private-provider native generation and 33 actual Git
GET comparisons remain **separate historical evidence**, not the source of
the provider-neutral records used for this Markdown. The renewed records,
commands and compiled-part receipts are on an evidence-only branch, not
bundled into the release tree.

To reproduce from the exact shipped source in this checkout, first run
`lake exe cache get` with the pinned toolchain and mathlib revision. Build
the pinned `leanprover/doc-gen4` Git revision above with the same Lean
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
The source revision must identify the exact analyzed `.lean`/config bytes,
even if a later commit only edits documentation. If it exists in Git, its
committed bytes are compared to every present input. A synthetic parentless
checkout without that object instead checks the regenerated manifest against
its own committed manifest and every current committed input and generator;
present-but-wrong history never triggers this fallback. The published
evidence records the native inputs, bytes, tool and checks. Source changes
require a fresh generation, not a stale manifest or parent assumption.

No HTML site, mathlib dependency pages, Lean `Init` pages, CDNs, JavaScript,
fonts or source scans ship in the Markdown release artifact. Their earlier
native diagnostic output and explicit dependency-link limitations remain
development evidence rather than a claim about this source-only package.
The adapted generator acknowledges Atlas's accepted multivariate-polynomials
and quadratic-algebras recipes and Anchor's original ideal-completion recipe;
earlier code acceptances do not review this exact generated candidate.

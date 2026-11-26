# Standalone reproduction

## Public inputs

The source of the study is the frozen 73-file ZIP with SHA-256 `4fecd3792e47752374062e5340bd06f2f1ed59d25c2132df7c8df97243bcfc86`. The public repository stores these files under [study/](study/) with their original byte hashes. The six numbered statements and their parameter domains are preserved. To rebuild that exact ZIP from a checkout, choose a new output filename:

```sh
python -B scripts/package_release.py --output ../alternating-gaussian-chains-v1.0.1.zip
```

The standalone acceptance used Windows x64 and CPython 3.12.10. A new virtual environment installed all eleven pinned plotting wheels from PyPI. Elan installed Lean 4.28.0 from its public release into a new toolchain directory. The independent typesetting check used Tectonic 0.17.0, an initially empty Tectonic cache, both pinned Noto fonts downloaded from their public revision, and the official v33 bundle. The bundle identifier was `6ffe055852f8faf66c0acbe1a7fb27f87b869a90bad1204f3bf4d9683f597c7c`. [Toolchain and font pins](study/README.md) · [Historical source hashes](study/upstream-files.sha256)

## Commands

With the tools from the [README](README.md) installed, the normal entry point obtains its sources and writes all generated files under the new work directory:

```sh
python -B study/reproduce.py all --work-dir ../chain-replay
```

For the shallow-checkout route, initialize the same work directory first. This avoids downloading the full Git histories of the math libraries. Use a fresh directory for a second clean Lean build.

```sh
python -B study/reproduce.py setup --work-dir ../chain-replay
python -B scripts/fetch_lean_packages.py --work-dir ../chain-replay
python -B study/reproduce.py all --work-dir ../chain-replay
```

The helper reads the hash-verified Lake manifest, fetches its commits and their declared release tags, and checks the nine resulting revisions. ProofWidgets uses the `v0.0.87` tag to find its public build archive. The initial Lean build must obtain the public mathlib cache; `--installed-dependencies` is for a later rebuild when the matching third-party build products already exist. Each run regenerates the twelve project modules and checks six axiom reports. The source of the four new formal statements is part of the ZIP.

### Windows tar diagnostic

On a Windows installation with a localized system tar, Lake may report `Tried to read from handle containing non UTF-8 data` when extracting ProofWidgets. In the acceptance run, Windows selected its system tar even with Git's tar on PATH. For that case, make Git's GNU tar visible in the new Lean *work* directory and keep its support DLLs on PATH. Run the following after setup, then run the public driver:

```powershell
$gitRoot = Split-Path (Split-Path (Get-Command git.exe).Source)
$gitTools = Join-Path $gitRoot 'usr/bin'
$env:PATH = "$gitTools;$env:PATH"
$env:LANG = 'C.UTF-8'
$env:LC_ALL = 'C.UTF-8'
$env:TAR_OPTIONS = '--force-local'
$workTar = '../chain-replay/lean/tar.exe'
if (-not (Test-Path -LiteralPath $workTar)) {
    Copy-Item -LiteralPath (Join-Path $gitTools 'tar.exe') -Destination $workTar
}
```

This copy belongs to the local build directory. It is outside the published source and release assets.

## Checks and scope

- **Source integrity.** Anonymous HTTPS retrieval of the 17 upstream inputs matched every SHA-256. All nine Lake repositories were fetched at their manifest commits. The Python, font and TeX inputs came from public endpoints. The independent packaging script recreated the named ZIP byte for byte.
- **Numerical evidence.** The eleven groups exercise 15 primary verifier programs, 16 main executable appendices, and three supplementary witnesses. The strict comparison covers 243 master-certificate lines, 21 supplementary witness lines and two lines for each rounding proof. The broad strip traversals visit 40,740 and 39,056 boxes; the width-22 atlas visits 5,638 boxes with six local leaves.
- **Documents and figures.** The regenerated English and Traditional Chinese PDFs match the frozen PDFs byte for byte, as do both phase figures. The documents have 12 and 10 pages respectively. Their Author fields, links, attachments and PDF objects were inspected along with the release payload. [Reference artifact digests](study/Reproduction.md)
- **Formal evidence.** The twelve historical project modules build with Lean 4.28.0. The two earlier four-site declarations and four alternating-moment declarations have the audited axiom sets. The global six-site classification additionally uses the analytic arguments and interval certificates. [Formal coverage](study/EVIDENCE.md)
- **Citation and licensing.** The CFF metadata was validated against the official v1.2.0 schema. The release carries separate notices for embedded font families; upstream source files lacking a redistribution grant are fetched by the reproduction program. [Citation schema](https://github.com/citation-file-format/citation-file-format/blob/1.2.0/schema.json) · [Rights and dependencies](THIRD-PARTY.md)

The [frozen reproduction report](study/Reproduction.md) records the earlier offline acceptance. Public dependency retrieval and a subsequent clean-clone replay are audited separately for this standalone distribution.

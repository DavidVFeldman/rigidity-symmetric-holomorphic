# Publishing recipe

1. Create the GitHub repository `DavidVFeldman/rigidity-symmetric-holomorphic`
   (public, no auto-generated files), add this directory's contents with
   GitHub Desktop, and push to `main`.
2. Wait for the CI check to go green (the first run builds Mathlib from the
   cache; expect roughly 20-40 minutes).
3. On Zenodo (Settings -> GitHub), flip the toggle for this repository.
4. On GitHub, create release `v1.0` ("Initial verified release"). Zenodo
   archives it and mints a version DOI and a concept DOI.
5. Backfill the concept DOI into README.md, CITATION.cff (add `doi:`), and
   the paper's Formal verification subsection (add the doi.org URL above the
   GitHub URL in the centered display); recompile the PDF; commit; release
   `v1.0.1` ("Record Zenodo DOI").
6. Confirm on the Zenodo record: both creators with affiliations, license
   CC-BY-4.0, type preprint.

# Submission manifest

## Primary manuscript

- Title: *Displaced-Zero Certificates and the Coefficient Mass of Polynomial Multiples*
- Source: `papers/coefficient-mass.tex`
- PDF: `papers/coefficient-mass.pdf` (generated; not tracked)
- Author: Bangyen Pham, Independent Researcher
- ORCID: 0009-0006-9928-2088
- 2020 MSC: Primary 11C08; Secondary 15B48, 26C05, 41A50
- Stable artifact DOI: https://doi.org/10.5281/zenodo.22998724

The seven other files in `papers/` are companion manuscripts, not parts of
this journal submission. They should not be uploaded as additional articles.
They may be supplied to an editor only when specifically requested.

## Venue sequence

Submit first to the **Journal of Number Theory**. The cover letter emphasizes
polynomial height, reduced-height consequences, and the prime-root asymptotic;
the real-root theorem is presented as the mechanism.

- If JNT rejects the paper as too analytic for its scope, submit next to the
  **Canadian Journal of Mathematics**.
- If JNT accepts the number-theory fit but rejects for priority or breadth,
  submit next to **Research in Number Theory**.

Do not submit simultaneously. The repository's prominent Lean material is
supporting verification, not the editorial pitch.

An arXiv preprint can be posted concurrently with journal review. Use primary
category `math.NT` and request a `math.CA` cross-list; see `submission/arxiv/`.

## Files for an initial JNT submission

- `submission/jnt/cover-letter.md`
- `submission/jnt/title-page.md`
- `submission/jnt/metadata.yml`
- `papers/coefficient-mass.pdf`
- `submission/suggested-reviewers.md` if the portal requests reviewers

The source supplement produced by `just submission` includes the pinned
proof-guard submodule and is self-contained with respect to repository
sources; third-party toolchains and caches still require downloads. Upload it
only as source or supplementary material when the portal permits it. The main
TeX file has an embedded bibliography and no external figures.

## Author checks before the final portal action

- Confirm the selected journal and its current author instructions.
- Confirm that this manuscript is not under consideration elsewhere.
- Review the generated PDF, cover letter, title page, abstract, keywords,
  classifications, declarations, and reviewer conflicts.
- Supply any postal address, phone number, or portal-only declarations that
  the author has not placed in the public repository.
- Confirm any named reviewer has no recent collaboration, institutional,
  supervisory, familial, or financial conflict with the author.
- Submit the exact tagged version and record the journal manuscript number.

Submitting through a journal or arXiv account is an external representational
act and remains a final author action. No submission has been made from this
repository.

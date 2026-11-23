# Collaboration statement

Team: Hagen, Preme and Farin Weinger (21-321, Fall 2026). Every member contributed
identifiable work, and the main design decisions were discussed as a team. AI use is
described separately in [AI_USE.md](AI_USE.md).

## Contributions

### Preme
- **Overall:** in terms of code I worked mainly on 3 files: Basic.lean, GaussianTilt.lean, and Walk.lean. In terms of the report, I wrote the second draft and curated it to become more motivating for readers without financial derivative context, and to make it more concise. Lastly, I wrote the script and created an html file to help my teammates prepare for the video recording. 
- **Definitions:** the time grid `TimeGrid` and the increments `Δt`, `girsanovDensity` and
  `girsanovMeasure` (`Girsanov/Basic.lean`).
- **Proofs:** the time-grid lemmas (`coe_Δt`, `Δt_pos`, `sum_Δt`, `T_nonneg`, ...), the
  Gaussian tilt lemmas in `Girsanov/GaussianTilt.lean`, and `girsanov_gaussian_partialSum`
  and `girsanov_walk` in `Girsanov/Walk.lean`.

### Hagen
- **Proofs:** the density API lemmas in `Girsanov/Basic.lean` (measurability, positivity,
  zero drift); the statements in `Girsanov/SingleTime.lean` and the proofs of
  `girsanov_single_time` and `isProbabilityMeasure_girsanovMeasure`.
- **Documentation:** the README (goal, principal theorem, file map, proved statements).
- **Report:** §1 and §3.
- **Video:** TODO (opening segment, editing, upload?).
- TODO (Hagen): check and complete.

### Farin Weinger
- **Definitions:** `tiltWeight`, `canonicalDensity` and `incrementLaw` (`Girsanov/Basic.lean`).
- **Proofs:** `pi_withDensity` (`Girsanov/DensityTransfer.lean`); `map_increments_eq_pi`,
  `incrementLaw_withDensity`, `girsanov_gaussian_pi`, `girsanov_increments` and the `n = 1`
  example (`Girsanov/FiniteTime.lean`); the canonical-density lemmas in `Girsanov/Basic.lean`;
  the proof of `map_withDensity_comp` in Hagen's `Girsanov/SingleTime.lean`.
- **Code:** the change to real-valued densities (commit `8cda85f`), which also changed
  Preme's `girsanovDensity` and replaced Hagen's `girsanovDensity_ne_zero` and
  `girsanovDensity_ne_top` with `girsanovDensity_pos`; removal of the duplicate `girsanov/`
  folder that broke CI.
- **Documentation:** module docstrings and Step · Fact · Mathlib name lists in her files;
  weekly updates to the README's list of proved statements.
- **Report:** set up the Overleaf project and LaTeX outline; wrote the abstract, §4, the
  bibliography and the Acknowledgements; my paragraph of the Reflections.
- **Video:** my segment on the n-step theorem and independence.
- **Statements:** collected this collaboration statement and the AI-use statement.

### Joint work
- `measurable_partialSum` in `Girsanov/Basic.lean` (Hagen, Farin, Preme).
- The weekly project plan, and the design of the shared definitions in `Girsanov/Basic.lean`.
- The Reflections section of the report, and the video script.

## Outside assistance
- The 21-321 course staff, whose feedback after the first checkpoint led us to simplify our
  definitions (one-step weight, product form, `abbrev`s).
- Pavel Kovalev, for the course textbook and the project template repository.

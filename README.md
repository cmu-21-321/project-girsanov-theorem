# Girsanov

A Lean 4 formalization of Girsanov's theorem for Brownian motion observed at finitely many
times, built on [Mathlib](https://github.com/leanprover-community/mathlib4).

## Goal

Let `0 = t₀ < t₁ < … < tₙ` be a time grid, and let the increments `ΔWₖ` be independent with
`ΔWₖ ∼ 𝒩(0, Δtₖ)` under `P`. Fix a drift `θ : Fin n → ℝ` and reweight `P` by

```
exp(-∑ₖ θₖ ΔWₖ - ½ ∑ₖ θₖ² Δtₖ).
```

Under the new measure `Q`, the drifted increments `ΔWₖ + θₖ Δtₖ` are again independent with
law `𝒩(0, Δtₖ)`. In other words, adding a drift to Brownian motion is the same as changing the
measure.

## Principal theorem

`Girsanov.girsanov_increments` in [Girsanov/FiniteTime.lean](Girsanov/FiniteTime.lean):

```lean
theorem girsanov_increments (hmeas : ∀ k, Measurable (ΔW k)) (hind : iIndepFun ΔW P)
    (hlaw : ∀ k, P.map (ΔW k) = gaussianReal 0 (g.Δt k)) (θ : Fin n → ℝ) :
    (girsanovMeasure P g θ ΔW).map (fun ω k ↦ ΔW k ω + θ k * (g.Δt k : ℝ))
      = incrementLaw g
```

Here `incrementLaw g = ⨂ₖ 𝒩(0, Δtₖ)`. Status: stated, not yet proved.

## File map

| File | Contents | Owner |
|---|---|---|
| [Girsanov/Basic.lean](Girsanov/Basic.lean) | Time grid, Girsanov density and measure | Preme |
| | Density API (measurability, positivity, zero drift), `partialSums` | Hagen |
| | Canonical density on `Fin n → ℝ`, `incrementLaw` | Farin |
| [Girsanov/DensityTransfer.lean](Girsanov/DensityTransfer.lean) | Product densities on product measures (`pi_withDensity`) | Farin |
| [Girsanov/SingleTime.lean](Girsanov/SingleTime.lean) | `map_withDensity_comp`, single-time Girsanov, `Q` is a probability measure | Hagen |
| [Girsanov/FiniteTime.lean](Girsanov/FiniteTime.lean) | Factoring the density, law of the increments, `girsanov_increments` | Farin |
| `Girsanov/GaussianTilt.lean` | `gaussianReal_withDensity_exp` (planned, not created yet) | unassigned |

## Proved statements

Last updated: 2026-10-28 (week 2). Update this list every week.

[Girsanov/Basic.lean](Girsanov/Basic.lean):

- `measurable_girsanovDensity`
- `girsanovDensity_ne_zero`
- `girsanovDensity_ne_top`
- `girsanovDensity_zero`
- `girsanovMeasure_zero`

Every other statement is still `sorry`.

## Setup

### Prerequisites

Install Lean via [elan](https://github.com/leanprover/elan) (see the
[Lean installation guide](https://lean-lang.org/install/)). The correct Lean version is
picked up automatically from `lean-toolchain`.

### 1. Rename the project

After creating your repository from this template, rename it from `ProjectTemplate` to your
own project name:

```bash
./customize.sh MyProject
```

This updates `lakefile.toml`, `lake-manifest.json`, the Lean imports and this README's title, and
renames `ProjectTemplate.lean` and `ProjectTemplate/` to `MyProject.lean` and `MyProject/`.
The name must be a valid Lean module name (letters, digits and underscores, starting with a
letter; UpperCamelCase is conventional). Commit the result, then delete `customize.sh`.

### 2. Get the Mathlib cache

Compiling Mathlib from source takes hours, so download the prebuilt files instead:

```bash
lake exe cache get
```

Re-run this whenever you change the Mathlib version (or if your editor starts rebuilding
Mathlib files).

### 3. Build and work on the project

```bash
lake build
```

- Put your Lean files under `MyProject/` and import each one from `MyProject.lean`, so that
  `lake build` (and CI) checks them.
- Open the repository folder (not a single file) in VS Code with the Lean 4 extension.

### Updating Mathlib

Change the `rev` under `[[require]]` in `lakefile.toml` to the new Mathlib tag, and set
`lean-toolchain` to match. Then run:

```bash
lake update mathlib
lake exe cache get
lake build
```

Alternatively, run the **Update Dependencies** workflow from the GitHub *Actions* tab: it
opens a pull request if the update builds, or an issue if it doesn't. (Uncomment the
`schedule` block in `.github/workflows/update.yml` to run it automatically.)

### GitHub setup

- **CI**: every push and pull request is built by `.github/workflows/lean_action_ci.yml`.
- To let the update workflow open pull requests, go to **Settings → Actions → General** and
  tick **Allow GitHub Actions to create and approve pull requests**.
- To publish docs to GitHub Pages, set **Settings → Pages → Source** to "GitHub Actions" and
  uncomment the `docgen-action` line in `lean_action_ci.yml`.

## Use of AI tools

Parts of this project were developed with the help of AI assistants (e.g. Claude by
Anthropic). We used them to:

- explain background mathematics and Lean/Mathlib concepts,
- search Mathlib for relevant lemmas and check their current names and signatures,
- draft Lean statements, proof outlines, and documentation, and
- help with project setup and tooling (Lean, Lake, git).

Every theorem statement in this repository was reviewed by a team member to confirm
it says what we intend, and every proof is checked by Lean: the project builds with
`lake build`, so no result depends on trusting an AI's output. Statements that are not
yet proved are marked with `sorry`.
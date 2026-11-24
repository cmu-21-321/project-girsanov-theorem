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

## Report

The written report is [report/report.pdf](report/report.pdf).

## Principal theorem

`Girsanov.girsanov_increments` in [Girsanov/FiniteTime.lean](Girsanov/FiniteTime.lean):

```lean
theorem girsanov_increments (hmeas : ∀ k, Measurable (ΔW k)) (hind : iIndepFun ΔW P)
    (hlaw : ∀ k, P.map (ΔW k) = gaussianReal 0 (g.Δt k)) (θ : Fin n → ℝ) :
    (girsanovMeasure P g θ ΔW).map (fun ω k ↦ ΔW k ω + θ k * (g.Δt k : ℝ))
      = incrementLaw g
```

Here `incrementLaw g = ⨂ₖ 𝒩(0, Δtₖ)`.

It is a corollary of a self-contained version, `Girsanov.girsanov_gaussian_pi`, which uses only
Mathlib notions (any finite index set, any variances `vₖ ≥ 0`, `Measure.withDensity` and
`Measure.pi`) and none of our own definitions:

```lean
theorem girsanov_gaussian_pi (v : ι → ℝ≥0) (hmeas : ∀ k, Measurable (X k))
    (hind : iIndepFun X P) (hlaw : ∀ k, P.map (X k) = gaussianReal 0 (v k)) (θ : ι → ℝ) :
    (P.withDensity fun ω ↦ ENNReal.ofReal
        (Real.exp (-(∑ k, θ k * X k ω) - (1 / 2) * ∑ k, θ k ^ 2 * (v k : ℝ)))).map
        (fun ω k ↦ X k ω + θ k * (v k : ℝ))
      = Measure.pi fun k ↦ gaussianReal 0 (v k)
```

## File map

| File | Contents | Owner |
|---|---|---|
| [Girsanov/Basic.lean](Girsanov/Basic.lean) | Time grid, Girsanov density and measure | Preme |
| | Density API (measurability, positivity, zero drift), `measurable_partialSum` | Hagen |
| | Canonical density on `Fin n → ℝ`, `incrementLaw` | Farin |
| [Girsanov/DensityTransfer.lean](Girsanov/DensityTransfer.lean) | Product densities on product measures (`pi_withDensity`) | Farin |
| [Girsanov/SingleTime.lean](Girsanov/SingleTime.lean) | `map_withDensity_comp`, single-time Girsanov, `Q` is a probability measure | Hagen |
| [Girsanov/FiniteTime.lean](Girsanov/FiniteTime.lean) | Factoring the density, law of the increments, `girsanov_increments` | Farin |
| [Girsanov/GaussianTilt.lean](Girsanov/GaussianTilt.lean) | Gaussian tilt lemma `gaussianReal_withDensity_tiltWeight` | Preme |

## Proved statements

Last updated: 2026-11-23 (final). Every statement below is proved; the project has no `sorry`.

[Girsanov/Basic.lean](Girsanov/Basic.lean):

- `TimeGrid.t_castSucc_lt_t_succ`, `TimeGrid.coe_Δt`, `TimeGrid.Δt_pos`, `TimeGrid.Δt_ne_zero`
- `TimeGrid.sum_succ_sub_castSucc`, `TimeGrid.sum_Δt`, `TimeGrid.T_nonneg`
- `measurable_girsanovDensity`
- `girsanovDensity_pos`
- `girsanovDensity_zero`
- `girsanovMeasure_zero`
- `measurable_tiltWeight`
- `tiltWeight_pos`
- `measurable_canonicalDensity`
- `canonicalDensity_eq_exp_sum`
- `girsanovDensity_eq_canonicalDensity_comp`
- `girsanovDensity_eq_prod`
- `measurable_partialSum`

[Girsanov/GaussianTilt.lean](Girsanov/GaussianTilt.lean):

- `gaussianPDFReal_mul_exp`
- `gaussianReal_withDensity_tiltWeight`

[Girsanov/DensityTransfer.lean](Girsanov/DensityTransfer.lean):

- `pi_withDensity` (with the private helper `indicator_univ_pi_prod`)

[Girsanov/FiniteTime.lean](Girsanov/FiniteTime.lean):

- `incrementLaw_withDensity`
- `prod_tiltWeight`
- `girsanov_gaussian_pi`
- `map_increments_eq_pi`
- `girsanov_increments`
- example: `n = 1` agrees with the single-time theorem

[Girsanov/SingleTime.lean](Girsanov/SingleTime.lean):

- `map_withDensity_comp`
- `girsanov_single_time`
- `isProbabilityMeasure_girsanovMeasure`
- example: `θ = 0` reduces `girsanov_single_time` to the hypothesis on the law of `W`

[Girsanov/Walk.lean](Girsanov/Walk.lean):

- `girsanov_gaussian_partialSum`
- `girsanov_walk`

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

## AI use and collaboration

See [AI_USE.md](AI_USE.md) for each team member's AI-use statement and
[COLLABORATION.md](COLLABORATION.md) for each member's contributions.

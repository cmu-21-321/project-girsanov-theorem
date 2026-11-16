import Girsanov.FiniteTime

/-!
# Girsanov for the walk

The walk is the sequence of partial sums of the increments: `W₀ = 0` and
`W_{j+1} = W_j + ΔW_j`. We use Mathlib's `Fin.partialSum` for it (see `Girsanov/Basic.lean`).

Under the Girsanov measure `Q`, the walk of the shifted increments `ΔW k + θ k * Δtₖ` has the
same law as the walk of the increments `ΔW k` under `P`.

## Main results

* `girsanov_gaussian_partialSum`: the self-contained version. It uses only Mathlib notions
  (`Measure.withDensity`, `gaussianReal`, `Fin.partialSum`) and any variances `vₖ ≥ 0`.
* `girsanov_walk`: the version for a time grid. It is `girsanov_gaussian_partialSum` with
  `vₖ = Δtₖ`.

## Plan for `girsanov_gaussian_partialSum`

1. Under `Q`, the law of the shifted increment vector is `Measure.pi fun k ↦ 𝒩(0, vₖ)`
   (`girsanov_gaussian_pi`).
2. Under `P`, the law of the increment vector is the same product measure (independence).
3. So the two increment vectors have the same law. Map both laws by `Fin.partialSum`.
4. Mapping by the increment vector and then by `Fin.partialSum` is mapping by the walk
   (`Measure.map_map`).

## Step · Fact · Mathlib name

* Step 1. Law of the shifted increments under `Q`: `girsanov_gaussian_pi` (Farin).
* Step 2. `iIndepFun f μ ↔ μ.map (fun ω i ↦ f i ω) = Measure.pi fun i ↦ μ.map (f i)`:
  `iIndepFun_iff_map_fun_eq_pi_map`.
* Step 4. `(μ.map f).map g = μ.map (g ∘ f)` for measurable `f` and `g`: `Measure.map_map`.
* Step 4. `Fin.partialSum` is measurable: `measurable_partialSum` (Girsanov/Basic.lean).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Girsanov

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

-- Author: Preme.

/-- **Girsanov for partial sums of independent Gaussians.** Let `X k ∼ 𝒩(0, vₖ)` be
independent under `P`. Reweight `P` by `exp(-∑ₖ θₖ Xₖ - ½ ∑ₖ θₖ² vₖ)`. Under the new measure,
the partial sums of the shifted variables `X k + θₖ vₖ` have the law that the partial sums
of the `X k` have under `P`. -/
theorem girsanov_gaussian_partialSum {X : Fin n → Ω → ℝ} (v : Fin n → ℝ≥0)
    (hmeas : ∀ k, Measurable (X k)) (hind : iIndepFun X P)
    (hlaw : ∀ k, P.map (X k) = gaussianReal 0 (v k)) (θ : Fin n → ℝ) :
    (P.withDensity fun ω ↦ ENNReal.ofReal
        (Real.exp (-(∑ k, θ k * X k ω) - (1 / 2) * ∑ k, θ k ^ 2 * (v k : ℝ)))).map
        (fun ω ↦ Fin.partialSum fun k ↦ X k ω + θ k * (v k : ℝ))
      = P.map (fun ω ↦ Fin.partialSum fun k ↦ X k ω) := by
  have hY : Measurable fun ω k ↦ X k ω := measurable_pi_iff.2 hmeas
  change (P.withDensity _).map (Fin.partialSum ∘ fun ω k ↦ X k ω + θ k * (v k : ℝ))
    = P.map (Fin.partialSum ∘ fun ω k ↦ X k ω)
  rw [← Measure.map_map measurable_partialSum (by fun_prop),
    ← Measure.map_map measurable_partialSum hY,
    girsanov_gaussian_pi v hmeas hind hlaw θ,
    (iIndepFun_iff_map_fun_eq_pi_map fun k ↦ (hmeas k).aemeasurable).1 hind]
  simp only [hlaw]

/-- **Girsanov for the walk.** Under `Q`, the walk with the shifted increments
`ΔW k + θ k * Δtₖ` has the law that the walk with the increments `ΔW k` has under `P`.

This is `girsanov_gaussian_partialSum` with the variances `Δtₖ` of the time grid. -/
theorem girsanov_walk (g : TimeGrid n) {ΔW : Fin n → Ω → ℝ} (hmeas : ∀ k, Measurable (ΔW k))
    (hind : iIndepFun ΔW P) (hlaw : ∀ k, P.map (ΔW k) = gaussianReal 0 (g.Δt k))
    (θ : Fin n → ℝ) :
    (girsanovMeasure P g θ ΔW).map
        (fun ω ↦ Fin.partialSum fun k ↦ ΔW k ω + θ k * (g.Δt k : ℝ))
      = P.map (fun ω ↦ Fin.partialSum fun k ↦ ΔW k ω) :=
  girsanov_gaussian_partialSum g.Δt hmeas hind hlaw θ

/-- **Example (θ = 0).** If the drift is `0`, then the Girsanov measure is `P`: nothing is
reweighted and nothing is shifted. -/
example (g : TimeGrid n) (ΔW : Fin n → Ω → ℝ) : girsanovMeasure P g 0 ΔW = P :=
  girsanovMeasure_zero g ΔW P

end Girsanov

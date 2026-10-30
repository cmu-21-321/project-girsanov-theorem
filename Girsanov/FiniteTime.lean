import Girsanov.Basic
import Girsanov.DensityTransfer

/-!
# Girsanov for finitely many observation times

Under `P`, the increments `ΔW k` are independent with `ΔW k ∼ 𝒩(0, Δtₖ)`.
Under the Girsanov measure `Q = girsanovMeasure P g θ ΔW`, the shifted increments
`ΔW k + θ k * Δtₖ` have that same law, `incrementLaw g = ⨂ₖ 𝒩(0, Δtₖ)`.

## Step · Fact · Mathlib name

* Indep. `iIndepFun f μ ↔ μ.map (fun ω i ↦ f i ω) = Measure.pi fun i ↦ μ.map (f i)`
  (needs `IsProbabilityMeasure μ` and `AEMeasurable` components):
  `iIndepFun_iff_map_fun_eq_pi_map`.
* Independence. The coordinates are independent under `Measure.pi`: `iIndepFun_pi`.
* Shift. `(Measure.pi μ).map (fun x i ↦ f i (x i)) = Measure.pi fun i ↦ (μ i).map (f i)`:
  `Measure.pi_map_pi`.
* Shift. `(gaussianReal μ v).map (· + y) = gaussianReal (μ + y) v`:
  `gaussianReal_map_add_const`.
* Probability. `Measure.pi` of probability measures is a probability measure:
  instance `Measure.pi.instIsProbabilityMeasure` (found automatically for `incrementLaw`,
  which is an `abbrev`).

`iIndepFun` takes the family and the measure only: `iIndepFun ΔW P`
(no explicit `MeasurableSpace` argument in this Mathlib version).

## Plan for `girsanov_increments`

1. By `map_increments_eq_pi`, the law of the increment vector under `P` is `incrementLaw g`.
2. `Q` reweights `P` by `canonicalDensity g θ ∘ (increment vector)`
   (`girsanovDensity_eq_canonicalDensity_comp`), so `map_withDensity_comp` turns
   the law under `Q` into `(incrementLaw g).withDensity (canonicalDensity g θ)`.
3. `canonicalDensity` is already a product of `tiltWeight`s, so `incrementLaw_withDensity`
   (an instance of `pi_withDensity`) splits it into one tilted Gaussian per step.
4. Tilt each coordinate with `gaussianReal_withDensity_exp`: coordinate `k` is
   `𝒩(-θₖ Δtₖ, Δtₖ)`.
5. Shift every coordinate by `θₖ Δtₖ` with `Measure.pi_map_pi` and
   `gaussianReal_map_add_const`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Girsanov

variable {n : ℕ}

#check @Measure.pi_eq
#check @withDensity_apply
#check @MeasurableSet.univ_pi
#check @Measure.restrict_pi_pi
#check @iIndepFun_iff_map_fun_eq_pi_map
#check @iIndepFun_pi
#check @Measure.pi_map_pi
#check @gaussianReal_map_add_const
#check @Real.exp_sum
#check @ENNReal.ofReal_prod_of_nonneg
#check @SigmaFinite.withDensity_of_ne_top'
#check @Measure.pi_map_eval

/-- The Girsanov-reweighted increment law splits into one tilted Gaussian per step. -/
theorem incrementLaw_withDensity (g : TimeGrid n) (θ : Fin n → ℝ) :
    (incrementLaw g).withDensity (canonicalDensity g θ)
      = Measure.pi fun k ↦ (gaussianReal 0 (g.Δt k)).withDensity (tiltWeight (θ k) (g.Δt k)) :=
  pi_withDensity (fun k ↦ measurable_tiltWeight _ _) (fun k ↦ tiltWeight_ne_top _ _)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (g : TimeGrid n) {ΔW : Fin n → Ω → ℝ}

/-- Independent Gaussian increments have the product law `incrementLaw g`. (Week 3) -/
theorem map_increments_eq_pi (hmeas : ∀ k, Measurable (ΔW k)) (hind : iIndepFun ΔW P)
    (hlaw : ∀ k, P.map (ΔW k) = gaussianReal 0 (g.Δt k)) :
    P.map (fun ω k ↦ ΔW k ω) = incrementLaw g := by
  -- `rw [(iIndepFun_iff_map_fun_eq_pi_map fun k ↦ (hmeas k).aemeasurable).1 hind]`,
  -- then `simp only [hlaw, incrementLaw]`.
  sorry

/-- **Girsanov for the increments.** Under `Q`, the shifted increments
`ΔW k + θ k * Δtₖ` are independent with law `𝒩(0, Δtₖ)`. (Week 4) -/
theorem girsanov_increments (hmeas : ∀ k, Measurable (ΔW k)) (hind : iIndepFun ΔW P)
    (hlaw : ∀ k, P.map (ΔW k) = gaussianReal 0 (g.Δt k)) (θ : Fin n → ℝ) :
    (girsanovMeasure P g θ ΔW).map (fun ω k ↦ ΔW k ω + θ k * (g.Δt k : ℝ))
      = incrementLaw g := by
  -- Needs `map_withDensity_comp` (Girsanov/SingleTime.lean) and
  -- `gaussianReal_withDensity_exp` (Girsanov/GaussianTilt.lean): add those imports in Week 4.
  sorry

end Girsanov

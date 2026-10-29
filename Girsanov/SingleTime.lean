import Girsanov.Basic

/-!
# Girsanov at a single time

Under `P` let `W ∼ 𝒩(0, T)`. Reweighting `P` by `exp(-θ W - θ² T / 2)` gives a measure `Q`
under which `W + θ T ∼ 𝒩(0, T)`. This file also has the change-of-variables lemma
`map_withDensity_comp` used in `girsanov_increments`, and the fact that the Girsanov
measure is a probability measure.

## Step · Fact · Mathlib name

* Pushforward. `μ.map f s = μ (f ⁻¹' s)` for measurable `f` and `s`: `Measure.map_apply`.
* Pushforward. `∫⁻ a in s, g a ∂(μ.map f) = ∫⁻ x in f ⁻¹' s, g (f x) ∂μ`: `setLIntegral_map`.
* Density. `μ.withDensity f s = ∫⁻ a in s, f a ∂μ` for measurable `s`: `withDensity_apply`.
* Mass. `μ.withDensity f univ = ∫⁻ a, f a ∂μ`: `withDensity_apply _ MeasurableSet.univ`,
  then `Measure.restrict_univ`.
* Tilt. `𝒩(0, T).withDensity (exp(-θ x - θ² T / 2)) = 𝒩(-θ T, T)`:
  `gaussianReal_withDensity_exp` (Girsanov/GaussianTilt.lean, not written yet).
* Shift. `(gaussianReal μ v).map (· + y) = gaussianReal (μ + y) v`:
  `gaussianReal_map_add_const`.

## Plan for `map_withDensity_comp`

`ext s hs`, then `rw [Measure.map_apply hX hs, withDensity_apply _ (hX hs),
withDensity_apply _ hs, setLIntegral_map hs hf hX]`, and the two sides agree.

## Plan for `girsanov_single_time`

1. `map_withDensity_comp` with `f x = ofReal (exp(-θ x - θ² T / 2))` turns the law of `W`
   under `Q` into `𝒩(0, T).withDensity f`.
2. The Gaussian tilt makes this `𝒩(-θ T, T)`.
3. `Measure.map_map` and `gaussianReal_map_add_const` shift it to `𝒩(0, T)`.

## Plan for `isProbabilityMeasure_girsanovMeasure`

Use `girsanovDensity_eq_canonicalDensity_comp` and `map_withDensity_comp` to rewrite the
total mass as `(incrementLaw g).withDensity (canonicalDensity g θ) univ`, then factor and
tilt each coordinate as in `girsanov_increments`: each factor has mass `1`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

#check @Measure.map_apply
#check @setLIntegral_map
#check @withDensity_apply
#check @Measure.restrict_univ
#check @gaussianReal_map_add_const

namespace Girsanov

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- Reweighting by a density that factors through `X` and then pushing forward along `X`
is the same as pushing forward first and reweighting the law of `X`. -/
theorem map_withDensity_comp (P : Measure Ω) {X : Ω → α} (hX : Measurable X)
    {f : α → ℝ≥0∞} (hf : Measurable f) :
    (P.withDensity (f ∘ X)).map X = (P.map X).withDensity f := by
  sorry

/-- **Girsanov at a single time.** If `W ∼ 𝒩(0, T)` under `P`, then under
`Q = P.withDensity (exp(-θ W - θ² T / 2))` the shifted variable `W + θ T` is `𝒩(0, T)`. -/
theorem girsanov_single_time (P : Measure Ω) {W : Ω → ℝ} (hW : Measurable W) (T : ℝ≥0)
    (hlaw : P.map W = gaussianReal 0 T) (θ : ℝ) :
    (P.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (-θ * W ω - θ ^ 2 * T / 2))).map
        (fun ω ↦ W ω + θ * T)
      = gaussianReal 0 T := by
  sorry

/-- For independent Gaussian increments, the Girsanov measure is a probability measure. -/
theorem isProbabilityMeasure_girsanovMeasure {n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (g : TimeGrid n) {ΔW : Fin n → Ω → ℝ} (hmeas : ∀ k, Measurable (ΔW k))
    (hind : iIndepFun ΔW P) (hlaw : ∀ k, P.map (ΔW k) = gaussianReal 0 (g.Δt k))
    (θ : Fin n → ℝ) :
    IsProbabilityMeasure (girsanovMeasure P g θ ΔW) := by
  sorry

end Girsanov

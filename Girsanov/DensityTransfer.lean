import Girsanov.Basic

/-!
# Product densities on product measures

Let each factor `μ i` have the density `f i`.
Then the product measure with the density `x ↦ ∏ i, f i (x i)` is equal to
the product of the factors with their densities.
With this result, we can examine the Girsanov density on `Fin n → ℝ`
one coordinate at a time.

## Plan for `pi_withDensity`

1. Two σ-finite measures on the product are equal if they are equal on each box
   `Set.univ.pi s` with measurable sides (`Measure.pi_eq`).
2. On a box, the left side is `∫⁻ x in Set.univ.pi s, ∏ i, f i (x i) ∂(Measure.pi μ)`
   (`withDensity_apply`, `MeasurableSet.univ_pi`).
3. The integral over the box is equal to the integral of the box indicator over all points.
   The box indicator is the product `∏ i, (s i).indicator (f i) (x i)`
   (helper `indicator_univ_pi_prod`).
   The coordinates are independent under `Measure.pi`. Thus the integral of this product
   is the product of the integrals.
   Factor `i` uses only coordinate `i`. The law of coordinate `i` under `Measure.pi μ` is
   `μ i`. Thus factor `i` is `∫⁻ y in s i, f i y ∂(μ i)`.
4. Each factor `∫⁻ y in s i, f i y ∂(μ i)` is `(μ i).withDensity (f i) (s i)`
   (`withDensity_apply` again).

## Step · Fact · Mathlib name

* Setup. `μ.withDensity f` is σ-finite if `μ` is σ-finite and `f` is never `∞`:
  `SigmaFinite.withDensity_of_ne_top'`.
* Step 1. `Measure.pi μ = μ'` if the two measures are equal on boxes: `Measure.pi_eq`.
* Step 2. `μ.withDensity f s = ∫⁻ a in s, f a ∂μ` for a measurable `s`: `withDensity_apply`.
* Step 2. A box with measurable sides is measurable: `MeasurableSet.univ_pi`.
* Step 3a. `∫⁻ a in s, f a ∂μ = ∫⁻ a, s.indicator f a ∂μ`: `lintegral_indicator`.
* Step 3a. The value of an indicator inside and outside its set: `Set.indicator_of_mem`,
  `Set.indicator_of_notMem`. A product with a factor of zero is zero: `Finset.prod_eq_zero`.
* Step 3b. The coordinates are independent under `Measure.pi`: `iIndepFun_pi`.
* Step 3b. For independent random variables with values in `ℝ≥0∞`, `∫⁻ ∏ = ∏ ∫⁻`:
  `lintegral_prod_eq_prod_lintegral_of_indepFun`.
* Step 3c. For probability measures, the image of `Measure.pi μ` under `Function.eval i`
  is `μ i`: `measurePreserving_eval`. Change of variables: `MeasurePreserving.lintegral_comp`.

Note on step 3: Mathlib has the Bochner version `MeasureTheory.integral_fintype_prod_eq_prod`.
Mathlib does not have the `ℝ≥0∞` (`∫⁻`) version. For this reason, we use independence.
This method is correct only if each `μ i` is a probability measure.
This condition is true for us, because each factor is a Gaussian.
For a general σ-finite `μ`, use induction on `n` with
`MeasureTheory.measurePreserving_piFinSuccAbove` and `MeasureTheory.lintegral_prod_mul`.
This method is more work. Use it only if we send the lemma to Mathlib.
The first plan used `Measure.restrict_pi_pi` and `Measure.pi_map_eval`.
The final proof does not use them.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Girsanov

/-- On a box, the indicator of a product function is equal to the product of the
indicators of the coordinates. -/
private lemma indicator_univ_pi_prod {ι : Type*} [Fintype ι] (s : ι → Set ℝ)
    (f : ι → ℝ → ℝ≥0∞) (x : ι → ℝ) :
    (Set.univ.pi s).indicator (fun y ↦ ∏ i, f i (y i)) x = ∏ i, (s i).indicator (f i) (x i) := by
  by_cases hx : x ∈ Set.univ.pi s
  · -- Inside the box, each indicator is equal to its function.
    have hxi : ∀ i, x i ∈ s i := fun i ↦ hx i (Set.mem_univ i)
    simp [Set.indicator_of_mem hx, Set.indicator_of_mem (hxi _)]
  · -- Outside the box, there is a coordinate `j` with `x j ∉ s j`.
    -- That factor is `0`. A product with a factor of `0` is `0`.
    obtain ⟨j, hj⟩ : ∃ j, x j ∉ s j := by simpa [Set.mem_univ_pi] using hx
    rw [Set.indicator_of_notMem hx]
    exact (Finset.prod_eq_zero (Finset.mem_univ j) (Set.indicator_of_notMem hj _)).symm

/-- A product density on a product of probability measures is equal to the product of
the factor densities. Each `f i` is never `∞`. Thus each factor with its density is
σ-finite. -/
theorem pi_withDensity {ι : Type*} [Fintype ι]
    {μ : ι → Measure ℝ} [∀ i, IsProbabilityMeasure (μ i)]
    {f : ι → ℝ → ℝ≥0∞} (hf : ∀ i, Measurable (f i)) (hf_top : ∀ i x, f i x ≠ ∞) :
    (Measure.pi μ).withDensity (fun x ↦ ∏ i, f i (x i))
      = Measure.pi fun i ↦ (μ i).withDensity (f i) := by
  have : ∀ i, SigmaFinite ((μ i).withDensity (f i)) :=
    fun i ↦ SigmaFinite.withDensity_of_ne_top' (hf_top i)
  -- Step 1: Two measures on the product are equal if they are equal on each box `univ.pi s`.
  symm
  refine Measure.pi_eq fun s hs ↦ ?_
  -- Steps 2 and 4: Write the two sides as integrals of the densities over the box and
  -- over its sides.
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  simp_rw [withDensity_apply _ (hs _)]
  -- Goal: `∫⁻ x in univ.pi s, ∏ i, f i (x i) ∂(pi μ) = ∏ i, ∫⁻ y in s i, f i y ∂(μ i)`.
  -- Step 3a: Change the integral over the box into the integral of the box indicator
  -- over all points. Then write the box indicator as a product of one indicator for each
  -- coordinate.
  rw [← lintegral_indicator (MeasurableSet.univ_pi hs)]
  simp_rw [indicator_univ_pi_prod s f]
  -- Step 3b: The coordinates are independent under `Measure.pi`. Thus the integral of
  -- the product is the product of the integrals.
  have hmeas : ∀ i, Measurable ((s i).indicator (f i)) := fun i ↦ (hf i).indicator (hs i)
  have hind : iIndepFun (fun i (x : ι → ℝ) ↦ (s i).indicator (f i) (x i)) (Measure.pi μ) :=
    iIndepFun_pi fun i ↦ (hmeas i).aemeasurable
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _ hind
    fun i ↦ (hmeas i).comp (measurable_pi_apply i)]
  -- Step 3c: Factor `i` uses only coordinate `i`. The law of coordinate `i` under `pi μ`
  -- is `μ i`. Then change the indicator back into an integral over `s i`.
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [(measurePreserving_eval μ i).lintegral_comp (hmeas i), lintegral_indicator (hs i)]

end Girsanov
